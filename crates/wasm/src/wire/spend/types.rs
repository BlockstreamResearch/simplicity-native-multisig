use serde::{Deserialize, Serialize};

use super::super::types::{MultisigSession, WireUtxo};

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct WireOutput {
    pub(super) kind: WireOutputKind,
    pub(super) script_pubkey: Option<String>,
    pub(super) address: Option<String>,
    pub(super) asset: String,
    pub(super) value: u64,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) enum WireOutputKind {
    Transfer,
    Burn,
    Fee,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct WireVoteInput {
    pub(super) participant_index: usize,
    pub(super) signature_hex: String,
    pub(super) utxo: WireUtxo,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct WireTxOutSecrets {
    pub(super) asset: String,
    pub(super) value: u64,
    pub(super) asset_blinding_factor: String,
    pub(super) value_blinding_factor: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct SpendPlan {
    pub(super) session: MultisigSession,
    pub(super) proposed_pset_base64: String,
    pub(super) multisig_utxos: Vec<WireUtxo>,
    pub(super) vote_inputs: Vec<WireVoteInput>,
    pub(super) total_proposed_outputs: u16,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ExecutorFundedSpendPlan {
    #[serde(flatten)]
    pub(super) spend: SpendPlan,
    pub(super) executor_pset_base64: String,
    pub(super) executor_input_secrets: Vec<WireTxOutSecrets>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct PreparedSpendPlan {
    #[serde(flatten)]
    pub(super) spend: SpendPlan,
    pub(super) prepared_pset_base64: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct ProposalResult<'a> {
    pub(super) pset_base64: &'a str,
    pub(super) tx_hex: &'a str,
    pub(super) total_proposed_outputs: u16,
    pub(super) message_hash: &'a str,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct PsetResult<'a> {
    pub(super) pset_base64: &'a str,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct FinalizedSpendResult<'a> {
    pub(super) pset_base64: &'a str,
    pub(super) tx_hex: &'a str,
    pub(super) txid: &'a str,
}
