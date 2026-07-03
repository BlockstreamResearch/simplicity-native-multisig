//! On-chain coordination for vote proposals.
//!
//! Multisig data can be coordinated off-chain or through `OP_RETURN` outputs in
//! the transaction that locks funds to `vote.simf`.
//!
//! Version 1 only carries enough public, non-confidential data for another
//! participant or indexer to recognize the exact message being signed.
//! Confidential transport is left out of scope because it needs shared
//! blinding material and correct range proof handling.
//!
//! The encoder is paired with [`crate::vote::message`]: it publishes the
//! participant signature and sanitized proposal transaction needed to
//! reconstruct the same base and participant hashes in a deterministic,
//! chunked `OP_RETURN` payload.

use simplicityhl::elements::Transaction;
use simplicityhl::elements::confidential;
use simplicityhl::elements::pset::{Output, PartiallySignedTransaction};
use simplicityhl::elements::secp256k1_zkp::schnorr::Signature;

use crate::common::chunked_records::{RECORD_HEADER_LEN, RecordFraming};

const FRAMING: RecordFraming = RecordFraming {
    magic: b"SIMPVOTE",
    version: 1,
    metadata_kind: 0,
    chunk_kind: 2,
    label: "vote proposal",
};
const RECORD_SIGNATURE: u8 = 1;
const SIGNATURE_RECORD_LEN: usize = RECORD_HEADER_LEN + 64;

/// Vote proposal reconstructed from on-chain encoder outputs.
pub struct DecodedVote {
    /// Rebuilt PSET for the proposed transaction.
    pub proposed_pst: PartiallySignedTransaction,
    /// Participant signature over the vote message.
    pub participant_signature: Signature,
}

/// Encode a proposal PSET into PSET outputs that can be appended to a vote PSET.
///
/// The encoded bytes are the extracted proposal transaction, not the original
/// PSET metadata. The participant signature is stored in a separate
/// `OP_RETURN` record so an executor can recover both the proposal and the
/// signature from the vote transaction.
///
/// Decoding reconstructs a fresh PSET from that transaction, so
/// [`crate::vote::message::base_message_and_input_count`] sees the same
/// transaction shape and returns the same base message hash.
pub fn encode(
    proposed_pst: &PartiallySignedTransaction,
    participant_signature: Signature,
) -> anyhow::Result<Vec<Output>> {
    let proposal_tx = proposed_pst.extract_tx()?;
    let carrier_asset = proposal_tx
        .output
        .iter()
        .find_map(|output| match output.asset {
            confidential::Asset::Explicit(asset) => Some(asset),
            confidential::Asset::Null | confidential::Asset::Confidential(_) => None,
        })
        .ok_or_else(|| {
            anyhow::anyhow!(
                "proposal must contain at least one explicit output asset for OP_RETURN carriers"
            )
        })?;
    let proposal_bytes = simplicityhl::elements::encode::serialize(&proposal_tx);

    let mut signature = FRAMING.record_prefix(RECORD_SIGNATURE);
    signature.extend_from_slice(&participant_signature.serialize());

    let mut records = FRAMING.encode_payload(&proposal_bytes)?;
    records.insert(1, signature);

    Ok(records
        .iter()
        .map(|record| RecordFraming::record_output(record, carrier_asset))
        .collect())
}

/// Decode a proposal PSET from a transaction carrying encoder `OP_RETURN` outputs.
pub fn decode(transaction: &Transaction) -> anyhow::Result<DecodedVote> {
    let mut participant_signature = None;
    let proposal_bytes = FRAMING.decode_transaction(transaction, |kind, payload| {
        if kind != RECORD_SIGNATURE {
            anyhow::bail!("unsupported vote proposal record type");
        }
        if payload.len() != SIGNATURE_RECORD_LEN {
            anyhow::bail!("invalid vote proposal signature record length");
        }
        let signature = Signature::from_slice(&payload[RECORD_HEADER_LEN..])?;
        if participant_signature.replace(signature).is_some() {
            anyhow::bail!("duplicate vote proposal signature record");
        }

        Ok(())
    })?;

    let participant_signature = participant_signature
        .ok_or_else(|| anyhow::anyhow!("missing vote proposal signature record"))?;
    let proposal_tx = simplicityhl::elements::encode::deserialize(&proposal_bytes)?;

    Ok(DecodedVote {
        proposed_pst: PartiallySignedTransaction::from_tx(proposal_tx),
        participant_signature,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vote::message::{base_message_and_input_count, participant_message};
    use simplicityhl::elements::hashes::Hash;
    use simplicityhl::elements::pset::Input;
    use simplicityhl::elements::schnorr::Keypair;
    use simplicityhl::elements::secp256k1_zkp::SECP256K1;
    use simplicityhl::elements::secp256k1_zkp::{Message, SecretKey};
    use simplicityhl::elements::taproot::{LeafVersion, TapLeafHash};
    use simplicityhl::elements::{AssetId, LockTime, OutPoint, Script, Txid};

    #[test]
    fn round_trip_preserves_participant_message_hash() -> anyhow::Result<()> {
        let multisig_script = Script::new_op_return(b"multisig");
        let carrier_asset = AssetId::from_slice(&[1; 32])?;
        let mut proposal = PartiallySignedTransaction::new_v2();

        for index in 0..2 {
            let mut input =
                Input::from_prevout(OutPoint::new(Txid::from_slice(&[index; 32])?, index.into()));
            input.final_script_sig = Some(multisig_script.clone());
            proposal.add_input(input);
        }

        let mut non_prefix_input =
            Input::from_prevout(OutPoint::new(Txid::from_slice(&[3; 32])?, 0));
        non_prefix_input.final_script_sig = Some(Script::new_op_return(b"not-multisig"));
        proposal.add_input(non_prefix_input);

        proposal.add_output(Output::new_explicit(
            Script::new_op_return(b"recipient-a"),
            42,
            carrier_asset,
            None,
        ));
        proposal.add_output(Output::new_explicit(
            Script::new_op_return(b"recipient-b"),
            7,
            carrier_asset,
            None,
        ));

        let proposed_tx = proposal.extract_tx()?;
        let leaf_hash =
            TapLeafHash::from_script(&Script::new_op_return(b"vote"), LeafVersion::default());
        let (base_before, _) = base_message_and_input_count(&proposed_tx, &multisig_script, 2)?;
        let hash_before = participant_message(leaf_hash, base_before);
        let signer = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[11; 32])?);
        let participant_signature =
            signer.sign_schnorr(Message::from_digest(hash_before.to_byte_array()));

        let encoded_outputs = encode(&proposal, participant_signature)?;
        let carrier_tx = Transaction {
            version: 2,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: encoded_outputs
                .into_iter()
                .map(|output| output.to_txout())
                .collect(),
        };

        let decoded = decode(&carrier_tx)?;
        let decoded_tx = decoded.proposed_pst.extract_tx()?;
        let (base_after, _) = base_message_and_input_count(&decoded_tx, &multisig_script, 2)?;
        let hash_after = participant_message(leaf_hash, base_after);

        assert_eq!(base_before, base_after);
        assert_eq!(hash_before, hash_after);
        assert_eq!(participant_signature, decoded.participant_signature);

        Ok(())
    }
}
