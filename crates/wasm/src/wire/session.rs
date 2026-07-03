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

/// Script pubkey, address, and LWK watch descriptor of a multisig covenant,
/// shared by the session and descriptor wire formats.
struct MultisigIdentity {
    script_pubkey: String,
    address: String,
    /// LWK accepts a raw script pubkey watch descriptor in the form `:<script hex>`.
    lwk_descriptor: String,
}

fn multisig_identity(builder: &MultisigBuilder) -> anyhow::Result<MultisigIdentity> {
    let script = builder.script_pubkey()?;
    let script_pubkey = script_hex(&script);
    let address = Address::from_script(&script, None, &AddressParams::LIQUID_TESTNET)
        .ok_or_else(|| anyhow::anyhow!("multisig script pubkey is not addressable"))?
        .to_string();
    let lwk_descriptor = format!(":{script_pubkey}");

    Ok(MultisigIdentity {
        script_pubkey,
        address,
        lwk_descriptor,
    })
}

pub(super) fn session_from_parts(
    threshold: u32,
    participant_pubkeys: Vec<String>,
    participant_descriptors: Vec<String>,
    builder: &MultisigBuilder,
) -> anyhow::Result<String> {
    let identity = multisig_identity(builder)?;
    let participants = participant_pubkeys
        .into_iter()
        .zip(participant_descriptors)
        .enumerate()
        .map(
            |(index, (x_only_public_key, announced_descriptor))| SessionParticipant {
                index,
                x_only_public_key,
                vote_descriptor: watch_descriptor(&announced_descriptor),
            },
        )
        .collect();

    to_json(&MultisigSession {
        version: 1,
        network: "liquid-testnet".to_owned(),
        threshold,
        participants,
        multisig_script_pubkey: identity.script_pubkey,
        multisig_address: identity.address,
        lwk_descriptor: identity.lwk_descriptor,
    })
}

/// Convert an announced public participant descriptor into a wallet descriptor
/// that LWK can scan.
///
/// Announcements deliberately exclude blinding material, but LWK wallets only
/// accept CT descriptors, so scanning uses an ELIP-151 derived blinding key:
/// it is computed deterministically from the public descriptor, so wrapping
/// adds no secret material. Single-chain `/0/*` descriptors are also widened
/// to the standard `<0;1>` multipath so vote transactions funded from change
/// outputs stay discoverable.
fn watch_descriptor(announced: &str) -> String {
    let announced = announced.trim();
    let widened = announced
        .strip_suffix("/0/*)")
        .map_or_else(|| announced.to_owned(), |base| format!("{base}/<0;1>/*)"));
    if widened.starts_with("ct(") {
        widened
    } else {
        format!("ct(elip151,{widened})")
    }
}

pub(super) fn multisig_descriptor_from_parts(
    threshold: u32,
    participant_pubkeys: Vec<String>,
    builder: &MultisigBuilder,
) -> anyhow::Result<String> {
    let identity = multisig_identity(builder)?;
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
        multisig_script_pubkey: identity.script_pubkey,
        multisig_address: identity.address,
        lwk_descriptor: identity.lwk_descriptor,
    })
}

/// Rebuild the multisig covenant from wire fields and verify that the claimed
/// script pubkey matches the rebuilt one.
fn validated_builder(
    version: u8,
    network: &str,
    threshold: u32,
    participant_pubkeys: &[String],
    claimed_script_pubkey: &str,
    label: &str,
) -> anyhow::Result<MultisigBuilder> {
    if version != 1 {
        anyhow::bail!("unsupported {label} version");
    }
    if network != "liquid-testnet" {
        anyhow::bail!("only liquid-testnet is supported");
    }
    if participant_pubkeys.len() != PARTICIPANT_COUNT {
        anyhow::bail!("expected {PARTICIPANT_COUNT} participants");
    }

    let builder = multisig_builder(threshold, participant_pubkeys)?;
    if script_hex(&builder.script_pubkey()?) != claimed_script_pubkey {
        anyhow::bail!("{label} script does not match threshold and participants");
    }

    Ok(builder)
}

pub(super) fn session_builder(session: &MultisigSession) -> anyhow::Result<MultisigBuilder> {
    let participant_pubkeys = session
        .participants
        .iter()
        .map(|participant| participant.x_only_public_key.clone())
        .collect::<Vec<_>>();

    validated_builder(
        session.version,
        &session.network,
        session.threshold,
        &participant_pubkeys,
        &session.multisig_script_pubkey,
        "session",
    )
}

pub(super) fn descriptor_builder(
    descriptor: &MultisigDescriptor,
) -> anyhow::Result<MultisigBuilder> {
    let participant_pubkeys = descriptor
        .participants
        .iter()
        .map(|participant| participant.x_only_public_key.clone())
        .collect::<Vec<_>>();

    validated_builder(
        descriptor.version,
        &descriptor.network,
        descriptor.threshold,
        &participant_pubkeys,
        &descriptor.multisig_script_pubkey,
        "multisig descriptor",
    )
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
