//! String and JSON oriented API for FFI and browser bindings.
//!
//! The core SDK uses strongly typed Elements and Simplicity values.  This module
//! adapts those values to stable strings so native bindings, Wasm bindings, and
//! frontend code can stay thin.

use std::collections::HashMap;
use std::str::FromStr;

use contracts::common::{Utxo, op_return_payload};
use contracts::multisig::{MultisigBuilder, PARTICIPANT_COUNT};
use contracts::sdk::{
    VoteInput, create_proposed_multisig_spend, create_vote, finalize_multisig_spend,
    finalize_prepared_multisig_spend, prepare_multisig_spend_inputs,
};
use contracts::vote::onchain_encoder;
use elements::confidential::{self, AssetBlindingFactor, ValueBlindingFactor};
use elements::hashes::{Hash, sha256};
use elements::pset::{Output, PartiallySignedTransaction};
use elements::secp256k1_zkp::rand::thread_rng;
use elements::secp256k1_zkp::schnorr::Signature;
use elements::secp256k1_zkp::{Message, SECP256K1};
use elements::{
    Address, AddressParams, AssetId, BlockHash, OutPoint, Script, Transaction, TxOut, TxOutSecrets,
    TxOutWitness, Txid,
};

const LIQUID_TESTNET_GENESIS_BYTES: [u8; 32] = [
    0xc1, 0xb1, 0x6a, 0xe2, 0x4f, 0x24, 0x23, 0xae, 0xa2, 0xea, 0x34, 0x55, 0x22, 0x92, 0x79, 0x3b,
    0x5b, 0x5e, 0x82, 0x99, 0x9a, 0x1e, 0xed, 0x81, 0xd5, 0x6a, 0xee, 0x52, 0x8e, 0xda, 0x71, 0xa7,
];

mod announcement;
mod session;
mod spend;
mod types;
mod util;
mod vote;

use self::session::{descriptor_builder, session_builder, session_from_parts};
use self::types::{
    DescriptorParticipant, MultisigDescriptor, MultisigSession, SessionParticipant, WireUtxo,
};
use self::util::{
    derive_keypair, matching_participant_keypair, pset_from_base64, script_from_hex, script_hex,
    signature_from_hex, to_json, x_only_pubkey_from_hex,
};

pub use self::announcement::{
    append_participant_announcement_outputs, create_session_from_participant_announcements,
    decode_participant_announcement_transaction,
};
pub use self::session::{
    create_multisig_descriptor, derive_participant_key, inspect_multisig_descriptor,
    liquid_testnet_info,
};
pub use self::spend::{
    create_proposed_spend, finalize_prepared_spend_plan, finalize_spend_plan,
    prepare_executor_funded_spend,
};
pub use self::vote::{
    append_vote_carrier_outputs, create_signed_vote, decode_vote_transaction,
    decode_vote_transaction_auto,
};

#[cfg(test)]
mod tests;
