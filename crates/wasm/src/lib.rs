//! WASM bindings for Simplicity Native Multisig.

#![allow(clippy::missing_errors_doc, clippy::needless_pass_by_value)]

use wasm_bindgen::prelude::*;

mod wire;

#[wasm_bindgen(js_name = liquidTestnetInfo)]
pub fn liquid_testnet_info() -> Result<String, JsValue> {
    map_result(wire::liquid_testnet_info())
}

#[wasm_bindgen(js_name = deriveParticipantKey)]
pub fn derive_participant_key(mnemonic: String, account: u32) -> Result<String, JsValue> {
    map_result(wire::derive_participant_key(&mnemonic, account))
}

#[wasm_bindgen(js_name = createMultisigDescriptor)]
pub fn create_multisig_descriptor(
    threshold: u32,
    participant_pubkeys_json: String,
) -> Result<String, JsValue> {
    map_result(wire::create_multisig_descriptor(
        threshold,
        &participant_pubkeys_json,
    ))
}

#[wasm_bindgen(js_name = inspectMultisigDescriptor)]
pub fn inspect_multisig_descriptor(multisig_descriptor_json: String) -> Result<String, JsValue> {
    map_result(wire::inspect_multisig_descriptor(&multisig_descriptor_json))
}

#[wasm_bindgen(js_name = appendParticipantAnnouncementOutputs)]
pub fn append_participant_announcement_outputs(
    announcement_pset_base64: String,
    multisig_descriptor_json: String,
    participant_descriptor: String,
    mnemonic: String,
) -> Result<String, JsValue> {
    map_result(wire::append_participant_announcement_outputs(
        &announcement_pset_base64,
        &multisig_descriptor_json,
        &participant_descriptor,
        &mnemonic,
    ))
}

#[wasm_bindgen(js_name = decodeParticipantAnnouncementTransaction)]
pub fn decode_participant_announcement_transaction(
    multisig_descriptor_json: String,
    tx_hex: String,
) -> Result<String, JsValue> {
    map_result(wire::decode_participant_announcement_transaction(
        &multisig_descriptor_json,
        &tx_hex,
    ))
}

#[wasm_bindgen(js_name = createSessionFromParticipantAnnouncements)]
pub fn create_session_from_participant_announcements(
    multisig_descriptor_json: String,
    announcements_json: String,
) -> Result<String, JsValue> {
    map_result(wire::create_session_from_participant_announcements(
        &multisig_descriptor_json,
        &announcements_json,
    ))
}

#[wasm_bindgen(js_name = createProposedSpend)]
pub fn create_proposed_spend(
    session_json: String,
    utxos_json: String,
    outputs_json: String,
) -> Result<String, JsValue> {
    map_result(wire::create_proposed_spend(
        &session_json,
        &utxos_json,
        &outputs_json,
    ))
}

#[wasm_bindgen(js_name = createSignedVote)]
pub fn create_signed_vote(
    session_json: String,
    proposed_pset_base64: String,
    multisig_utxos_json: String,
    total_proposed_outputs: u16,
    mnemonic: String,
) -> Result<String, JsValue> {
    map_result(wire::create_signed_vote(
        &session_json,
        &proposed_pset_base64,
        &multisig_utxos_json,
        total_proposed_outputs,
        &mnemonic,
    ))
}

#[wasm_bindgen(js_name = appendVoteCarrierOutputs)]
pub fn append_vote_carrier_outputs(
    vote_pset_base64: String,
    proposed_pset_base64: String,
    participant_signature_hex: String,
) -> Result<String, JsValue> {
    map_result(wire::append_vote_carrier_outputs(
        &vote_pset_base64,
        &proposed_pset_base64,
        &participant_signature_hex,
    ))
}

#[wasm_bindgen(js_name = decodeVoteTransaction)]
pub fn decode_vote_transaction(
    session_json: String,
    tx_hex: String,
    total_proposed_outputs: u16,
) -> Result<String, JsValue> {
    map_result(wire::decode_vote_transaction(
        &session_json,
        &tx_hex,
        total_proposed_outputs,
    ))
}

#[wasm_bindgen(js_name = decodeVoteTransactionAuto)]
pub fn decode_vote_transaction_auto(
    session_json: String,
    tx_hex: String,
) -> Result<String, JsValue> {
    map_result(wire::decode_vote_transaction_auto(&session_json, &tx_hex))
}

#[wasm_bindgen(js_name = finalizeSpendPlan)]
pub fn finalize_spend_plan(plan_json: String) -> Result<String, JsValue> {
    map_result(wire::finalize_spend_plan(&plan_json))
}

#[wasm_bindgen(js_name = prepareExecutorFundedSpend)]
pub fn prepare_executor_funded_spend(plan_json: String) -> Result<String, JsValue> {
    map_result(wire::prepare_executor_funded_spend(&plan_json))
}

#[wasm_bindgen(js_name = finalizePreparedSpendPlan)]
pub fn finalize_prepared_spend_plan(plan_json: String) -> Result<String, JsValue> {
    map_result(wire::finalize_prepared_spend_plan(&plan_json))
}

fn map_result(result: anyhow::Result<String>) -> Result<String, JsValue> {
    result.map_err(|error| JsValue::from_str(&error.to_string()))
}
