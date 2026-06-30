use std::str::FromStr;

use bip39::Mnemonic;
use elements::Script;
use elements::bitcoin::bip32::{DerivationPath, Xpriv};
use elements::bitcoin::{NetworkKind, secp256k1};
use elements::pset::PartiallySignedTransaction;
use elements::schnorr::{Keypair, XOnlyPublicKey};
use elements::secp256k1_zkp::schnorr::Signature;
use elements::secp256k1_zkp::{SECP256K1, SecretKey};
use serde::Serialize;

pub(super) fn pset_from_base64(pset_base64: &str) -> anyhow::Result<PartiallySignedTransaction> {
    PartiallySignedTransaction::from_str(pset_base64.trim()).map_err(anyhow::Error::msg)
}

pub(super) fn derive_keypair(mnemonic: &str, account: u32) -> anyhow::Result<(Keypair, String)> {
    let mnemonic = Mnemonic::parse_normalized(mnemonic.trim())?;
    let seed = mnemonic.to_seed("");
    let path = format!("m/86h/1h/{account}h/0/0");
    let derivation_path = DerivationPath::from_str(&path)?;
    let xpriv = Xpriv::new_master(NetworkKind::Test, &seed)?;
    let child = xpriv.derive_priv(&secp256k1::Secp256k1::new(), &derivation_path)?;
    let secret_key = SecretKey::from_slice(&child.private_key.secret_bytes())?;

    Ok((Keypair::from_secret_key(SECP256K1, &secret_key), path))
}

pub(super) fn matching_participant_keypair<P>(
    participants: &[P],
    mnemonic: &str,
    error_message: &str,
    account: impl Fn(&P) -> usize,
    x_only_public_key: impl Fn(&P) -> &str,
) -> anyhow::Result<(usize, Keypair, String)> {
    for (participant_index, participant) in participants.iter().enumerate() {
        let (keypair, path) = derive_keypair(mnemonic, u32::try_from(account(participant))?)?;
        if hex::encode(keypair.x_only_public_key().0.serialize()) == x_only_public_key(participant)
        {
            return Ok((participant_index, keypair, path));
        }
    }

    anyhow::bail!("{error_message}")
}

pub(super) fn x_only_pubkey_from_hex(hex_value: &str) -> anyhow::Result<XOnlyPublicKey> {
    XOnlyPublicKey::from_slice(&hex::decode(hex_value.trim())?).map_err(anyhow::Error::msg)
}

pub(super) fn signature_from_hex(hex_value: &str) -> anyhow::Result<Signature> {
    Signature::from_slice(&hex::decode(hex_value.trim())?).map_err(anyhow::Error::msg)
}

pub(super) fn script_from_hex(hex_value: &str) -> anyhow::Result<Script> {
    Ok(Script::from(hex::decode(hex_value.trim())?))
}

pub(super) fn script_hex(script: &Script) -> String {
    format!("{script:x}")
}

pub(super) fn to_json(value: &impl Serialize) -> anyhow::Result<String> {
    serde_json::to_string_pretty(value).map_err(Into::into)
}
