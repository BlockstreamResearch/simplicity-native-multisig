#![allow(clippy::wildcard_imports)]

use serde::Serialize;

use super::*;

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SignedVoteResult<'a> {
    participant_index: usize,
    derivation_path: &'a str,
    x_only_public_key: &'a str,
    message_hash: &'a str,
    signature_hex: &'a str,
    vote_script_pubkey: &'a str,
    vote_address: &'a str,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct DecodedVoteResult<'a> {
    participant_index: usize,
    proposed_pset_base64: &'a str,
    proposed_tx_hex: &'a str,
    participant_signature_hex: &'a str,
    message_hash: &'a str,
    total_proposed_outputs: u16,
    proposal_input_outpoints: Vec<WireOutpoint>,
    vote_address: &'a str,
    vote_utxo: Option<WireUtxo>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct WireOutpoint {
    txid: String,
    vout: u32,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct CarrierAppendResult<'a> {
    pset_base64: &'a str,
}

/// Create and sign a vote for `proposed_pset_base64` using a participant mnemonic.
pub fn create_signed_vote(
    session_json: &str,
    proposed_pset_base64: &str,
    total_proposed_outputs: u16,
    mnemonic: &str,
) -> anyhow::Result<String> {
    let session: MultisigSession = serde_json::from_str(session_json)?;
    let builder = session_builder(&session)?;
    let proposed_pst = pset_from_base64(proposed_pset_base64)?;
    let (participant_index, keypair, path) = matching_participant_keypair(
        &session.participants,
        mnemonic,
        "mnemonic does not match any participant key in this session",
        |participant| participant.index,
        |participant| participant.x_only_public_key.as_str(),
    )?;
    let vote_plan = create_vote(&builder, &proposed_pst, total_proposed_outputs)?;
    let signed_vote = vote_plan.sign(&keypair);
    let vote_script_pubkey = signed_vote.script_pubkey()?;

    to_json(&SignedVoteResult {
        participant_index,
        derivation_path: &path,
        x_only_public_key: &session.participants[participant_index].x_only_public_key,
        message_hash: &vote_plan.message_hash().to_string(),
        signature_hex: &hex::encode(signed_vote.signature().serialize()),
        vote_script_pubkey: &script_hex(&vote_script_pubkey),
        vote_address: &vote_address(&vote_script_pubkey)?.to_string(),
    })
}

fn vote_address(vote_script_pubkey: &Script) -> anyhow::Result<Address> {
    Address::from_script(vote_script_pubkey, None, &AddressParams::LIQUID_TESTNET)
        .ok_or_else(|| anyhow::anyhow!("vote script pubkey is not addressable"))
}

/// Append encoded vote proposal records to an existing vote-funding PSET.
///
/// This is used with LWK's transaction builder: LWK selects and funds the vote
/// transaction, then this function appends the zero-value `OP_RETURN` carrier
/// outputs before the participant signer signs it.
pub fn append_vote_carrier_outputs(
    vote_pset_base64: &str,
    proposed_pset_base64: &str,
    participant_signature_hex: &str,
) -> anyhow::Result<String> {
    let mut vote_pst = pset_from_base64(vote_pset_base64)?;
    let proposed_pst = pset_from_base64(proposed_pset_base64)?;
    let participant_signature = signature_from_hex(participant_signature_hex)?;

    for output in onchain_encoder::encode(&proposed_pst, participant_signature)? {
        vote_pst.add_output(output);
    }

    to_json(&CarrierAppendResult {
        pset_base64: &vote_pst.to_string(),
    })
}

/// Decode a vote carrier transaction and recompute its participant message hash.
pub fn decode_vote_transaction(
    session_json: &str,
    tx_hex: &str,
    total_proposed_outputs: u16,
) -> anyhow::Result<String> {
    decode_vote_transaction_inner(session_json, tx_hex, Some(total_proposed_outputs))
}

/// Decode a vote carrier transaction and infer its signed proposal output count.
pub fn decode_vote_transaction_auto(session_json: &str, tx_hex: &str) -> anyhow::Result<String> {
    decode_vote_transaction_inner(session_json, tx_hex, None)
}

fn decode_vote_transaction_inner(
    session_json: &str,
    tx_hex: &str,
    total_proposed_outputs: Option<u16>,
) -> anyhow::Result<String> {
    let session: MultisigSession = serde_json::from_str(session_json)?;
    let builder = session_builder(&session)?;
    let tx: Transaction =
        simplicityhl::elements::encode::deserialize(&hex::decode(tx_hex.trim())?)?;
    let decoded = onchain_encoder::decode(&tx)?;
    let proposed_tx = decoded.proposed_pst.extract_tx()?;
    let total_proposed_outputs = total_proposed_outputs.map_or_else(
        || {
            let count = proposed_tx
                .output
                .iter()
                .position(|output| output.script_pubkey.is_empty())
                .unwrap_or(proposed_tx.output.len());
            u16::try_from(count).map_err(anyhow::Error::from)
        },
        Ok,
    )?;
    let vote_plan = create_vote(&builder, &decoded.proposed_pst, total_proposed_outputs)?;
    let participant_index = session
        .participants
        .iter()
        .position(|participant| {
            x_only_pubkey_from_hex(&participant.x_only_public_key)
                .and_then(|public_key| {
                    SECP256K1
                        .verify_schnorr(
                            &decoded.participant_signature,
                            &vote_plan.message(),
                            &public_key,
                        )
                        .map_err(anyhow::Error::msg)
                })
                .is_ok()
        })
        .ok_or_else(|| anyhow::anyhow!("vote signature does not match any session participant"))?;
    let signed_vote = vote_plan.signed_vote(decoded.participant_signature);
    let vote_script_pubkey = signed_vote.script_pubkey()?;
    let vote_utxo = tx
        .output
        .iter()
        .enumerate()
        .find(|(_, output)| output.script_pubkey == vote_script_pubkey)
        .map(|(vout, output)| {
            Ok::<_, anyhow::Error>(WireUtxo {
                txid: tx.txid().to_string(),
                vout: u32::try_from(vout)?,
                script_pubkey: script_hex(&output.script_pubkey),
                asset: explicit_asset_hex(output.asset)?,
                value: explicit_value(output.value)?,
            })
        })
        .transpose()?;
    let proposed_pset_base64 = decoded.proposed_pst.to_string();
    let proposed_tx_hex = hex::encode(simplicityhl::elements::encode::serialize(&proposed_tx));
    let proposal_input_outpoints = proposed_tx
        .input
        .iter()
        .map(|input| WireOutpoint {
            txid: input.previous_output.txid.to_string(),
            vout: input.previous_output.vout,
        })
        .collect();

    to_json(&DecodedVoteResult {
        participant_index,
        proposed_pset_base64: &proposed_pset_base64,
        proposed_tx_hex: &proposed_tx_hex,
        participant_signature_hex: &hex::encode(decoded.participant_signature.serialize()),
        message_hash: &vote_plan.message_hash().to_string(),
        total_proposed_outputs,
        proposal_input_outpoints,
        vote_address: &vote_address(&vote_script_pubkey)?.to_string(),
        vote_utxo,
    })
}

fn explicit_asset_hex(asset: confidential::Asset) -> anyhow::Result<String> {
    match asset {
        confidential::Asset::Explicit(asset) => Ok(asset.to_string()),
        confidential::Asset::Null | confidential::Asset::Confidential(_) => {
            anyhow::bail!("output asset must be explicit")
        }
    }
}

fn explicit_value(value: confidential::Value) -> anyhow::Result<u64> {
    match value {
        confidential::Value::Explicit(value) => Ok(value),
        confidential::Value::Null | confidential::Value::Confidential(_) => {
            anyhow::bail!("output value must be explicit")
        }
    }
}
