#![allow(clippy::wildcard_imports)]

use super::super::*;

use crate::wire::session::multisig_builder;
use serde::{Deserialize, Serialize};

pub(super) use simplicityhl::elements::LockTime;

pub const MNEMONIC: &str =
    "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";
pub const SECOND_MNEMONIC: &str =
    "letter advice cage absurd amount doctor acoustic avoid letter advice cage above";
pub const THIRD_MNEMONIC: &str = "zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo zoo wrong";
pub(super) const LIQUID_TESTNET_POLICY_ASSET: &str =
    "144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49";

pub(super) struct ProposalFixture {
    pub(super) session_json: String,
    pub(super) session: MultisigSession,
    pub(super) multisig_utxos: String,
    pub(super) proposal: ProposalResultForTest,
}

pub(super) const fn repeated_mnemonics() -> [&'static str; PARTICIPANT_COUNT] {
    [MNEMONIC, MNEMONIC, MNEMONIC]
}

pub(super) const fn distinct_mnemonics() -> [&'static str; PARTICIPANT_COUNT] {
    [MNEMONIC, SECOND_MNEMONIC, THIRD_MNEMONIC]
}

pub(super) fn participant_keys(
    mnemonics: [&str; PARTICIPANT_COUNT],
) -> anyhow::Result<Vec<String>> {
    mnemonics
        .iter()
        .enumerate()
        .map(|(index, mnemonic)| {
            let key = derive_participant_key(mnemonic, u32::try_from(index)?)?;
            let key: ParticipantKeyForTest = serde_json::from_str(&key)?;
            Ok(key.x_only_public_key)
        })
        .collect()
}

pub(super) fn blinded_dummy_descriptors() -> Vec<String> {
    (0..PARTICIPANT_COUNT)
        .map(|index| {
            format!(
                "ct(slip77({}),elwpkh([00000000/84h/1h/{index}h]tpubDUMMY/0/*))",
                "0".repeat(64)
            )
        })
        .collect()
}

pub(super) fn session(
    mnemonics: [&str; PARTICIPANT_COUNT],
) -> anyhow::Result<(String, MultisigSession)> {
    let participant_pubkeys = participant_keys(mnemonics)?;
    let builder = multisig_builder(2, &participant_pubkeys)?;

    let session_json = session_from_parts(
        2,
        participant_pubkeys,
        blinded_dummy_descriptors(),
        &builder,
    )?;
    let session = serde_json::from_str(&session_json)?;

    Ok((session_json, session))
}

pub(super) fn multisig_utxos_json(session: &MultisigSession, value: u64) -> String {
    serde_json::json!([
        {
            "txid": "0101010101010101010101010101010101010101010101010101010101010101",
            "vout": 0,
            "scriptPubkey": session.multisig_script_pubkey,
            "asset": LIQUID_TESTNET_POLICY_ASSET,
            "value": value
        }
    ])
    .to_string()
}

pub(super) fn proposal_fixture(
    input_value: u64,
    transfer_value: u64,
    fee_value: u64,
) -> anyhow::Result<ProposalFixture> {
    let (session_json, session) = session(distinct_mnemonics())?;
    let multisig_utxos = multisig_utxos_json(&session, input_value);
    let outputs = serde_json::json!([
        {
            "kind": "transfer",
            "address": session.multisig_address,
            "asset": LIQUID_TESTNET_POLICY_ASSET,
            "value": transfer_value
        },
        {
            "kind": "fee",
            "asset": LIQUID_TESTNET_POLICY_ASSET,
            "value": fee_value
        }
    ])
    .to_string();
    let proposal_json = create_proposed_spend(&session_json, &multisig_utxos, &outputs)?;
    let proposal = serde_json::from_str(&proposal_json)?;

    Ok(ProposalFixture {
        session_json,
        session,
        multisig_utxos,
        proposal,
    })
}

pub(super) fn vote_inputs_json(
    session_json: &str,
    proposal: &ProposalResultForTest,
    mnemonics: [&str; PARTICIPANT_COUNT],
) -> anyhow::Result<String> {
    let first_vote: SignedVoteResultForTest = serde_json::from_str(&create_signed_vote(
        session_json,
        &proposal.pset_base64,
        proposal.total_proposed_outputs,
        mnemonics[0],
    )?)?;
    let second_vote: SignedVoteResultForTest = serde_json::from_str(&create_signed_vote(
        session_json,
        &proposal.pset_base64,
        proposal.total_proposed_outputs,
        mnemonics[1],
    )?)?;

    Ok(serde_json::json!([
        {
            "participantIndex": first_vote.participant_index,
            "signatureHex": first_vote.signature_hex,
            "utxo": {
                "txid": "0202020202020202020202020202020202020202020202020202020202020202",
                "vout": 0,
                "scriptPubkey": first_vote.vote_script_pubkey,
                "asset": LIQUID_TESTNET_POLICY_ASSET,
                "value": 1_000
            }
        },
        {
            "participantIndex": second_vote.participant_index,
            "signatureHex": second_vote.signature_hex,
            "utxo": {
                "txid": "0303030303030303030303030303030303030303030303030303030303030303",
                "vout": 0,
                "scriptPubkey": second_vote.vote_script_pubkey,
                "asset": LIQUID_TESTNET_POLICY_ASSET,
                "value": 1_000
            }
        }
    ])
    .to_string())
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ParticipantKeyForTest {
    pub(super) x_only_public_key: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ParticipantAnnouncementAppendResultForTest {
    pub(super) pset_base64: String,
    pub(super) participant_index: usize,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ParticipantAnnouncementForTest {
    pub(super) participant_index: usize,
    pub(super) x_only_public_key: String,
    pub(super) participant_descriptor: String,
    pub(super) signature_hex: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ProposalResultForTest {
    pub(super) pset_base64: String,
    pub(super) total_proposed_outputs: u16,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct DecodedVoteResultForTest {
    pub(super) participant_index: usize,
    pub(super) proposed_tx_hex: String,
    pub(super) total_proposed_outputs: u16,
    pub(super) proposal_input_outpoints: Vec<serde_json::Value>,
    pub(super) vote_utxo: WireUtxo,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct SignedVoteResultForTest {
    pub(super) participant_index: usize,
    pub(super) signature_hex: String,
    pub(super) vote_script_pubkey: String,
}
