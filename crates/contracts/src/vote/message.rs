//! Canonical messages signed by multisig participants.
//!
//! The covenant signs transaction shape rather than a free-form payload.
//!
//! The base message follows `multisig_n_of_3.simf`: collect the prefix of inputs
//! locked by the current multisig script, then append the proposed output
//! hashes.
//!
//! The participant message then binds that base message to the
//! executable vote leaf so the signature also commits to the checks enforced by
//! `vote.simf`.

use crate::common::multisig_input_prefix;

use simplicityhl::elements::encode;
use simplicityhl::elements::hashes::{Hash, HashEngine, sha256};
use simplicityhl::elements::taproot::TapLeafHash;
use simplicityhl::elements::{Script, Transaction};

fn input_hash(engine: &mut sha256::HashEngine, hash: &sha256::Hash) {
    engine.input(hash.as_byte_array());
}

fn input_confidential(
    engine: &mut sha256::HashEngine,
    serialized: &[u8],
    even_prefix: u8,
    odd_prefix: u8,
) {
    match serialized {
        [0x00] => engine.input(&[0x00]),
        [0x01, data @ ..] => {
            engine.input(&[0x01]);
            engine.input(data);
        }
        [prefix, data @ ..] => {
            engine.input(&[if prefix & 1 == 1 {
                odd_prefix
            } else {
                even_prefix
            }]);
            engine.input(data);
        }
        [] => unreachable!("serialized confidential values are never empty"),
    }
}

/// Build the base message and count the multisig input prefix.
///
/// The prefix rule is intentional: a participant signs the contiguous multisig
/// inputs at the beginning of the transaction.
///
/// A later input with the same script is outside the prefix
/// and is not part of the covenant's base message.
pub fn base_message_and_input_count(
    proposed_tx: &Transaction,
    multisig_script: &Script,
    total_proposed_outputs: u16,
) -> anyhow::Result<(sha256::Hash, u32)> {
    let mut engine = sha256::Hash::engine();
    let mut multisig_input_count = 0_u32;
    for input in multisig_input_prefix(proposed_tx, multisig_script) {
        if input.is_pegin {
            anyhow::bail!("pegin multisig inputs are unsupported");
        }

        let mut input_engine = sha256::Hash::engine();
        input_engine.input(&[0x00]);
        input_engine.input(input.previous_output.txid.as_byte_array());
        input_engine.input(&input.previous_output.vout.to_be_bytes());
        input_engine.input(&input.sequence.to_consensus_u32().to_be_bytes());
        input_engine.input(&[0x00]);
        input_hash(&mut engine, &sha256::Hash::from_engine(input_engine));
        multisig_input_count += 1;
    }

    if multisig_input_count == 0 {
        anyhow::bail!("at least one multisig input should be present");
    }

    for output in proposed_tx
        .output
        .iter()
        .take(usize::from(total_proposed_outputs))
    {
        let mut output_engine = sha256::Hash::engine();
        input_confidential(
            &mut output_engine,
            &encode::serialize(&output.asset),
            0x0a,
            0x0b,
        );
        input_confidential(
            &mut output_engine,
            &encode::serialize(&output.value),
            0x08,
            0x09,
        );
        input_confidential(
            &mut output_engine,
            &encode::serialize(&output.nonce),
            0x02,
            0x03,
        );
        input_hash(
            &mut output_engine,
            &sha256::Hash::hash(output.script_pubkey.as_bytes()),
        );

        let range_proof = output
            .witness
            .rangeproof
            .as_ref()
            .map(|proof| proof.serialize())
            .unwrap_or_default();
        input_hash(&mut output_engine, &sha256::Hash::hash(&range_proof));
        input_hash(&mut engine, &sha256::Hash::from_engine(output_engine));
    }

    Ok((sha256::Hash::from_engine(engine), multisig_input_count))
}

/// Bind the base message to the participant's executable vote leaf.
#[must_use]
pub fn participant_message(
    vote_executable_leaf_hash: TapLeafHash,
    base_message: sha256::Hash,
) -> sha256::Hash {
    let mut engine = sha256::Hash::engine();
    engine.input(vote_executable_leaf_hash.as_byte_array());
    input_hash(&mut engine, &base_message);
    sha256::Hash::from_engine(engine)
}
