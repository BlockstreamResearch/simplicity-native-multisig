use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct MultisigSession {
    pub(super) version: u8,
    pub(super) network: String,
    pub(super) threshold: u32,
    pub(super) participants: Vec<SessionParticipant>,
    pub(super) multisig_script_pubkey: String,
    pub(super) multisig_address: String,
    pub(super) lwk_descriptor: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct MultisigDescriptor {
    pub(super) version: u8,
    pub(super) network: String,
    pub(super) threshold: u32,
    pub(super) participants: Vec<DescriptorParticipant>,
    pub(super) multisig_script_pubkey: String,
    pub(super) multisig_address: String,
    pub(super) lwk_descriptor: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct DescriptorParticipant {
    pub(super) index: usize,
    pub(super) x_only_public_key: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct SessionParticipant {
    pub(super) index: usize,
    pub(super) x_only_public_key: String,
    pub(super) vote_descriptor: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct WireUtxo {
    pub(super) txid: String,
    pub(super) vout: u32,
    pub(super) script_pubkey: String,
    pub(super) asset: String,
    pub(super) value: u64,
}
