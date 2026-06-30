#![allow(clippy::wildcard_imports)]

use serde::Serialize;

use super::*;

const LIQUID_TESTNET_POLICY_ASSET: &str =
    "144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49";

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct LiquidTestnetInfo<'a> {
    network: &'a str,
    policy_asset: &'a str,
    genesis_hash: &'a str,
    default_esplora_url: &'a str,
    default_waterfalls_url: &'a str,
    explorer_tx_url_prefix: &'a str,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ParticipantKey<'a> {
    derivation_path: String,
    x_only_public_key: &'a str,
}

/// Liquid testnet constants used by the demo frontend.
pub fn liquid_testnet_info() -> anyhow::Result<String> {
    to_json(&LiquidTestnetInfo {
        network: "liquid-testnet",
        policy_asset: LIQUID_TESTNET_POLICY_ASSET,
        genesis_hash: &hex::encode(LIQUID_TESTNET_GENESIS_BYTES),
        default_esplora_url: "https://blockstream.info/liquidtestnet/api",
        default_waterfalls_url: "https://waterfalls.liquidwebwallet.org/liquidtestnet/api",
        explorer_tx_url_prefix: "https://blockstream.info/liquidtestnet/tx/",
    })
}

/// Derive the covenant participant key used by this demo from a BIP39 mnemonic.
///
/// The demo intentionally uses one fixed BIP86-style Liquid testnet path:
/// `m/86h/1h/{account}h/0/0`.
pub fn derive_participant_key(mnemonic: &str, account: u32) -> anyhow::Result<String> {
    let (keypair, path) = derive_keypair(mnemonic, account)?;
    let x_only_public_key = keypair.x_only_public_key().0;

    to_json(&ParticipantKey {
        derivation_path: path,
        x_only_public_key: &hex::encode(x_only_public_key.serialize()),
    })
}

/// Build a multisig-only descriptor.
pub fn create_multisig_descriptor(
    threshold: u32,
    participant_pubkeys_json: &str,
) -> anyhow::Result<String> {
    let participant_pubkeys: Vec<String> = serde_json::from_str(participant_pubkeys_json)?;
    if participant_pubkeys.len() != PARTICIPANT_COUNT {
        anyhow::bail!("expected {PARTICIPANT_COUNT} participant public keys");
    }

    let builder = multisig_builder(threshold, &participant_pubkeys)?;
    multisig_descriptor_from_parts(threshold, participant_pubkeys, &builder)
}

/// Validate and normalize a multisig-only descriptor JSON.
pub fn inspect_multisig_descriptor(descriptor_json: &str) -> anyhow::Result<String> {
    let descriptor: MultisigDescriptor = serde_json::from_str(descriptor_json)?;
    let builder = descriptor_builder(&descriptor)?;
    multisig_descriptor_from_parts(
        descriptor.threshold,
        descriptor
            .participants
            .iter()
            .map(|participant| participant.x_only_public_key.clone())
            .collect(),
        &builder,
    )
}

pub(super) fn session_from_parts(
    threshold: u32,
    participant_pubkeys: Vec<String>,
    participant_descriptors: Vec<String>,
    builder: &MultisigBuilder,
) -> anyhow::Result<String> {
    let multisig_script = builder.script_pubkey()?;
    let multisig_script_pubkey = script_hex(&multisig_script);
    let multisig_address =
        Address::from_script(&multisig_script, None, &AddressParams::LIQUID_TESTNET)
            .ok_or_else(|| anyhow::anyhow!("multisig script pubkey is not addressable"))?
            .to_string();
    let participants = participant_pubkeys
        .into_iter()
        .zip(participant_descriptors)
        .enumerate()
        .map(
            |(index, (x_only_public_key, vote_descriptor))| SessionParticipant {
                index,
                x_only_public_key,
                vote_descriptor,
            },
        )
        .collect();

    to_json(&MultisigSession {
        version: 1,
        network: "liquid-testnet".to_owned(),
        threshold,
        participants,
        multisig_script_pubkey: multisig_script_pubkey.clone(),
        multisig_address,
        lwk_descriptor: format!(":{multisig_script_pubkey}"),
    })
}

pub(super) fn multisig_descriptor_from_parts(
    threshold: u32,
    participant_pubkeys: Vec<String>,
    builder: &MultisigBuilder,
) -> anyhow::Result<String> {
    let multisig_script = builder.script_pubkey()?;
    let multisig_script_pubkey = script_hex(&multisig_script);
    let multisig_address =
        Address::from_script(&multisig_script, None, &AddressParams::LIQUID_TESTNET)
            .ok_or_else(|| anyhow::anyhow!("multisig script pubkey is not addressable"))?
            .to_string();
    let participants = participant_pubkeys
        .into_iter()
        .enumerate()
        .map(|(index, x_only_public_key)| DescriptorParticipant {
            index,
            x_only_public_key,
        })
        .collect();

    to_json(&MultisigDescriptor {
        version: 1,
        network: "liquid-testnet".to_owned(),
        threshold,
        participants,
        multisig_script_pubkey: multisig_script_pubkey.clone(),
        multisig_address,
        lwk_descriptor: format!(":{multisig_script_pubkey}"),
    })
}

pub(super) fn session_builder(session: &MultisigSession) -> anyhow::Result<MultisigBuilder> {
    if session.version != 1 {
        anyhow::bail!("unsupported session descriptor version");
    }
    if session.network != "liquid-testnet" {
        anyhow::bail!("only liquid-testnet is supported");
    }
    if session.participants.len() != PARTICIPANT_COUNT {
        anyhow::bail!("expected {PARTICIPANT_COUNT} participants");
    }

    let participant_pubkeys = session
        .participants
        .iter()
        .map(|participant| participant.x_only_public_key.clone())
        .collect::<Vec<_>>();
    let builder = multisig_builder(session.threshold, &participant_pubkeys)?;
    let script_pubkey = script_hex(&builder.script_pubkey()?);

    if script_pubkey != session.multisig_script_pubkey {
        anyhow::bail!("session multisig script does not match threshold and participants");
    }

    Ok(builder)
}

pub(super) fn descriptor_builder(
    descriptor: &MultisigDescriptor,
) -> anyhow::Result<MultisigBuilder> {
    if descriptor.version != 1 {
        anyhow::bail!("unsupported multisig descriptor version");
    }
    if descriptor.network != "liquid-testnet" {
        anyhow::bail!("only liquid-testnet is supported");
    }
    if descriptor.participants.len() != PARTICIPANT_COUNT {
        anyhow::bail!("expected {PARTICIPANT_COUNT} participants");
    }

    let participant_pubkeys = descriptor
        .participants
        .iter()
        .map(|participant| participant.x_only_public_key.clone())
        .collect::<Vec<_>>();
    let builder = multisig_builder(descriptor.threshold, &participant_pubkeys)?;
    let script_pubkey = script_hex(&builder.script_pubkey()?);

    if script_pubkey != descriptor.multisig_script_pubkey {
        anyhow::bail!("multisig descriptor script does not match threshold and participants");
    }

    Ok(builder)
}

pub(super) fn multisig_builder(
    threshold: u32,
    participant_pubkeys: &[String],
) -> anyhow::Result<MultisigBuilder> {
    let participants = [
        x_only_pubkey_from_hex(&participant_pubkeys[0])?,
        x_only_pubkey_from_hex(&participant_pubkeys[1])?,
        x_only_pubkey_from_hex(&participant_pubkeys[2])?,
    ];
    MultisigBuilder::new(threshold, participants)
}
