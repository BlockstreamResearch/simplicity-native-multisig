use crate::scripts::tap_data_hash;

use std::collections::HashMap;

use crate::constants::unspendable_internal_key;
use simplex::simplicityhl::elements::Script;
use simplex::simplicityhl::elements::bitcoin::secp256k1;
use simplex::simplicityhl::elements::hashes::{Hash, HashEngine, sha256};
use simplex::simplicityhl::elements::secp256k1_zkp::schnorr::Signature;
use simplex::simplicityhl::elements::taproot::TaprootBuilder;
use simplex::simplicityhl::num::U256;
use simplex::simplicityhl::simplicity::Cmr;
use simplex::simplicityhl::str::WitnessName;
use simplex::simplicityhl::value::UIntValue;
use simplex::simplicityhl::{Arguments, CompiledProgram, TemplateProgram};

pub const VOTE_SOURCE: &str = include_str!("../simf/vote.simf");

pub(super) fn get_vote_program(
    target_multisig: Script,
    is_debug_symbols_enabled: bool,
) -> anyhow::Result<CompiledProgram> {
    let template_program = TemplateProgram::new(VOTE_SOURCE).map_err(|e| anyhow::anyhow!(e))?;

    let mut eng = sha256::Hash::engine();
    eng.input(target_multisig.as_bytes());
    let target_multisig_hash = sha256::Hash::from_engine(eng);

    let args = Arguments::from(HashMap::from([(
        WitnessName::from_str_unchecked("TARGET_MULTISIG"),
        simplex::simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
            target_multisig_hash.as_byte_array().to_owned(),
        ))),
    )]));

    template_program
        .instantiate(args, is_debug_symbols_enabled)
        .map_err(|e| anyhow::anyhow!(e))
}

pub(super) fn taproot_spend_info(
    multisig_signature: Signature,
    cmr: Cmr,
) -> anyhow::Result<simplex::simplicityhl::elements::taproot::TaprootSpendInfo> {
    let (script, version) = (
        Script::from(cmr.as_ref().to_vec()),
        simplex::simplicityhl::simplicity::leaf_version(),
    );

    let mut eng = sha256::Hash::engine();
    eng.input(&multisig_signature.serialize());
    let state = sha256::Hash::from_engine(eng);

    let state_hash = tap_data_hash(&state.as_byte_array().to_vec());

    let builder = TaprootBuilder::new()
        .add_leaf_with_ver(1, script, version)
        .map_err(|e| anyhow::anyhow!(e))?
        .add_hidden(1, state_hash)
        .map_err(|e| anyhow::anyhow!(e))?;

    builder
        .finalize(secp256k1::SECP256K1, unspendable_internal_key())
        .map_err(|e| anyhow::anyhow!(e))
}

#[cfg(test)]
mod test {}
