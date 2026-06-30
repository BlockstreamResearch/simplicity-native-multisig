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

use simplicityhl::elements::confidential;
use simplicityhl::elements::hashes::{Hash, sha256};
use simplicityhl::elements::pset::{Output, PartiallySignedTransaction};
use simplicityhl::elements::secp256k1_zkp::schnorr::Signature;
use simplicityhl::elements::{AssetId, Script, Transaction};

use crate::common::op_return_payload;

const MAGIC: &[u8; 8] = b"SIMPVOTE";
const VERSION_V1: u8 = 1;
const CHECKSUM_LEN: usize = 32;
const SIGNATURE_LEN: usize = 64;
const VERSION_OFFSET: usize = MAGIC.len();
const RECORD_KIND_OFFSET: usize = VERSION_OFFSET + 1;
const RECORD_HEADER_LEN: usize = RECORD_KIND_OFFSET + 1;
const RECORD_METADATA: u8 = 0;
const RECORD_SIGNATURE: u8 = 1;
const RECORD_CHUNK: u8 = 2;
const METADATA_TOTAL_CHUNKS_OFFSET: usize = RECORD_HEADER_LEN;
const METADATA_TOTAL_LEN_OFFSET: usize = METADATA_TOTAL_CHUNKS_OFFSET + 2;
const METADATA_CHECKSUM_OFFSET: usize = METADATA_TOTAL_LEN_OFFSET + 4;
const METADATA_LEN: usize = METADATA_CHECKSUM_OFFSET + CHECKSUM_LEN;
const SIGNATURE_OFFSET: usize = RECORD_HEADER_LEN;
const SIGNATURE_RECORD_LEN: usize = SIGNATURE_OFFSET + SIGNATURE_LEN;
const CHUNK_INDEX_OFFSET: usize = RECORD_HEADER_LEN;
const CHUNK_DATA_OFFSET: usize = CHUNK_INDEX_OFFSET + 2;
const MAX_OP_RETURN_PAYLOAD_BYTES: usize = 75;
const MAX_CHUNK_DATA_BYTES: usize = MAX_OP_RETURN_PAYLOAD_BYTES - CHUNK_DATA_OFFSET;

/// Vote proposal reconstructed from on-chain encoder outputs.
pub struct DecodedVote {
    /// Rebuilt PSET for the proposed transaction.
    pub proposed_pst: PartiallySignedTransaction,
    /// Participant signature over the vote message.
    pub participant_signature: Signature,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Metadata {
    total_chunks: u16,
    total_len: u32,
    checksum: sha256::Hash,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Chunk {
    index: u16,
    data: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Record {
    Metadata(Metadata),
    Signature(Signature),
    Chunk(Chunk),
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
    let checksum = sha256::Hash::hash(&proposal_bytes);
    let total_len = u32::try_from(proposal_bytes.len())
        .map_err(|_| anyhow::anyhow!("encoded proposal is too large"))?;
    let total_chunks = proposal_bytes.len().div_ceil(MAX_CHUNK_DATA_BYTES);
    let total_chunks = u16::try_from(total_chunks)
        .map_err(|_| anyhow::anyhow!("encoded proposal needs too many outputs"))?;

    let mut metadata = record_prefix(RECORD_METADATA);
    metadata.extend_from_slice(&total_chunks.to_be_bytes());
    metadata.extend_from_slice(&total_len.to_be_bytes());
    metadata.extend_from_slice(checksum.as_byte_array());

    let mut signature = record_prefix(RECORD_SIGNATURE);
    signature.extend_from_slice(&participant_signature.serialize());

    let mut outputs = vec![
        record_output(&metadata, carrier_asset),
        record_output(&signature, carrier_asset),
    ];

    outputs.extend(proposal_bytes.chunks(MAX_CHUNK_DATA_BYTES).enumerate().map(
        |(index, chunk)| {
            let mut payload = record_prefix(RECORD_CHUNK);
            payload.extend_from_slice(
                &u16::try_from(index)
                    .expect("chunk count is already bounded")
                    .to_be_bytes(),
            );
            payload.extend_from_slice(chunk);

            record_output(&payload, carrier_asset)
        },
    ));

    Ok(outputs)
}

/// Decode a proposal PSET from a transaction carrying encoder `OP_RETURN` outputs.
pub fn decode(transaction: &Transaction) -> anyhow::Result<DecodedVote> {
    let mut records = Vec::new();
    for output in &transaction.output {
        let Some((payload, has_extra_pushes)) = op_return_payload(&output.script_pubkey) else {
            continue;
        };

        if payload.len() < MAGIC.len() || &payload[..MAGIC.len()] != MAGIC {
            continue;
        }

        if has_extra_pushes {
            anyhow::bail!("vote proposal OP_RETURN output contains extra pushes");
        }

        if payload.len() < RECORD_HEADER_LEN {
            anyhow::bail!("truncated vote proposal record header");
        }

        if payload[VERSION_OFFSET] != VERSION_V1 {
            anyhow::bail!("unsupported vote proposal encoding version");
        }

        match payload[RECORD_KIND_OFFSET] {
            RECORD_METADATA => {
                if payload.len() != METADATA_LEN {
                    anyhow::bail!("invalid vote proposal metadata record length");
                }

                let total_chunks = u16::from_be_bytes(
                    payload[METADATA_TOTAL_CHUNKS_OFFSET..METADATA_TOTAL_LEN_OFFSET]
                        .try_into()
                        .expect("slice length is checked by METADATA_LEN"),
                );
                let total_len = u32::from_be_bytes(
                    payload[METADATA_TOTAL_LEN_OFFSET..METADATA_CHECKSUM_OFFSET]
                        .try_into()
                        .expect("slice length is checked by METADATA_LEN"),
                );
                let checksum =
                    sha256::Hash::from_slice(&payload[METADATA_CHECKSUM_OFFSET..METADATA_LEN])?;

                records.push(Record::Metadata(Metadata {
                    total_chunks,
                    total_len,
                    checksum,
                }));
            }
            RECORD_SIGNATURE => {
                if payload.len() != SIGNATURE_RECORD_LEN {
                    anyhow::bail!("invalid vote proposal signature record length");
                }

                records.push(Record::Signature(Signature::from_slice(
                    &payload[SIGNATURE_OFFSET..SIGNATURE_RECORD_LEN],
                )?));
            }
            RECORD_CHUNK => {
                if payload.len() < CHUNK_DATA_OFFSET {
                    anyhow::bail!("truncated vote proposal chunk record");
                }

                let index = u16::from_be_bytes(
                    payload[CHUNK_INDEX_OFFSET..CHUNK_DATA_OFFSET]
                        .try_into()
                        .expect("slice length is checked by CHUNK_DATA_OFFSET"),
                );

                records.push(Record::Chunk(Chunk {
                    index,
                    data: payload[CHUNK_DATA_OFFSET..].to_vec(),
                }));
            }
            _ => anyhow::bail!("unsupported vote proposal record type"),
        }
    }

    if records.is_empty() {
        anyhow::bail!("transaction does not contain vote proposal records");
    }

    let mut metadata = None;
    let mut participant_signature = None;
    let mut chunks = Vec::new();

    for record in records {
        match record {
            Record::Metadata(next_metadata) => {
                if metadata.replace(next_metadata).is_some() {
                    anyhow::bail!("duplicate vote proposal metadata record");
                }
            }
            Record::Signature(next_signature) => {
                if participant_signature.replace(next_signature).is_some() {
                    anyhow::bail!("duplicate vote proposal signature record");
                }
            }
            Record::Chunk(chunk) => chunks.push(chunk),
        }
    }

    let metadata =
        metadata.ok_or_else(|| anyhow::anyhow!("missing vote proposal metadata record"))?;
    let participant_signature = participant_signature
        .ok_or_else(|| anyhow::anyhow!("missing vote proposal signature record"))?;

    if metadata.total_chunks == 0 {
        anyhow::bail!("vote proposal chunk count can not be zero");
    }

    let mut ordered = vec![None; usize::from(metadata.total_chunks)];
    for chunk in chunks {
        let index = usize::from(chunk.index);
        if index >= ordered.len() {
            anyhow::bail!("vote proposal chunk index is out of bounds");
        }

        if ordered[index].replace(chunk.data).is_some() {
            anyhow::bail!("duplicate vote proposal chunk");
        }
    }

    let mut proposal_bytes = Vec::with_capacity(usize::try_from(metadata.total_len)?);
    for (index, chunk) in ordered.into_iter().enumerate() {
        let chunk = chunk.ok_or_else(|| anyhow::anyhow!("missing vote proposal chunk {index}"))?;
        proposal_bytes.extend_from_slice(&chunk);
    }

    if proposal_bytes.len() != usize::try_from(metadata.total_len)? {
        anyhow::bail!("decoded vote proposal length mismatch");
    }

    if sha256::Hash::hash(&proposal_bytes) != metadata.checksum {
        anyhow::bail!("decoded vote proposal checksum mismatch");
    }

    let proposal_tx = simplicityhl::elements::encode::deserialize(&proposal_bytes)?;

    Ok(DecodedVote {
        proposed_pst: PartiallySignedTransaction::from_tx(proposal_tx),
        participant_signature,
    })
}

fn record_output(payload: &[u8], carrier_asset: AssetId) -> Output {
    debug_assert!(payload.len() <= MAX_OP_RETURN_PAYLOAD_BYTES);
    Output::new_explicit(Script::new_op_return(payload), 0, carrier_asset, None)
}

fn record_prefix(kind: u8) -> Vec<u8> {
    let mut payload = Vec::with_capacity(MAX_OP_RETURN_PAYLOAD_BYTES);
    payload.extend_from_slice(MAGIC);
    payload.push(VERSION_V1);
    payload.push(kind);
    payload
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vote::message::{base_message_and_input_count, participant_message};
    use simplicityhl::elements::pset::Input;
    use simplicityhl::elements::schnorr::Keypair;
    use simplicityhl::elements::secp256k1_zkp::SECP256K1;
    use simplicityhl::elements::secp256k1_zkp::{Message, SecretKey};
    use simplicityhl::elements::taproot::{LeafVersion, TapLeafHash};
    use simplicityhl::elements::{LockTime, OutPoint, Txid};

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
