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
    expected_multisig_inputs_count: u32,
    is_debug_symbols_enabled: bool,
) -> anyhow::Result<CompiledProgram> {
    let template_program = TemplateProgram::new(VOTE_SOURCE).map_err(|e| anyhow::anyhow!(e))?;

    let mut eng = sha256::Hash::engine();
    eng.input(target_multisig.as_bytes());
    let target_multisig_hash = sha256::Hash::from_engine(eng);

    let args = Arguments::from(HashMap::from([
        (
            WitnessName::from_str_unchecked("TARGET_MULTISIG"),
            simplex::simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
                target_multisig_hash.as_byte_array().to_owned(),
            ))),
        ),
        (
            WitnessName::from_str_unchecked("EXPECTED_MULTISIG_INPUTS_COUNT"),
            simplex::simplicityhl::Value::from(UIntValue::U32(expected_multisig_inputs_count)),
        ),
    ]));

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
mod test {
    use super::{get_vote_program, taproot_spend_info};
    use crate::runner::run_program;
    use crate::scripts::script_ver;

    use std::sync::Arc;

    use simplex::program::TrackerLogLevel;
    use simplex::simplicityhl::WitnessValues;
    use simplex::simplicityhl::elements::confidential::{Asset, Value};
    use simplex::simplicityhl::elements::hashes::Hash;
    use simplex::simplicityhl::elements::pset::{Input, PartiallySignedTransaction};
    use simplex::simplicityhl::elements::schnorr::Keypair;
    use simplex::simplicityhl::elements::secp256k1_zkp::rand::thread_rng;
    use simplex::simplicityhl::elements::secp256k1_zkp::{Message, SECP256K1, SecretKey};
    use simplex::simplicityhl::elements::taproot::ControlBlock;
    use simplex::simplicityhl::elements::{BlockHash, OutPoint, Script, Txid};
    use simplex::simplicityhl::simplicity::jet::elements::ElementsEnv;

    fn run_vote_with_inputs(
        target_script: Script,
        expected_multisig_inputs_count: u32,
        input_scripts: Vec<Script>,
    ) -> anyhow::Result<()> {
        let program = get_vote_program(target_script, expected_multisig_inputs_count, true)?;
        let cmr = program.commit().cmr();
        let (vote_script, vote_version) = script_ver(cmr);

        let signer = Keypair::from_secret_key(&SECP256K1, &SecretKey::new(&mut thread_rng()));
        let signature = signer.sign_schnorr(Message::from_digest([1; 32]));
        let spend_info = taproot_spend_info(signature, cmr)?;
        let vote_control_block = spend_info
            .control_block(&(vote_script, vote_version))
            .expect("Must retrieve control block for the vote script path");
        let vote_script_pubkey = Script::new_v1_p2tr_tweaked(spend_info.output_key());

        let mut pst = PartiallySignedTransaction::new_v2();
        for index in 0..input_scripts.len() {
            let outpoint = OutPoint::new(Txid::from_slice(&[index as u8; 32])?, 0);
            pst.add_input(Input::from_prevout(outpoint));
        }

        let vote_outpoint = OutPoint::new(Txid::from_slice(&[0xff; 32])?, 0);
        pst.add_input(Input::from_prevout(vote_outpoint));

        let tx = Arc::new(pst.extract_tx()?);
        let vote_input_index: u32 = input_scripts.len().try_into()?;

        let mut utxos = Vec::new();
        for script_pubkey in input_scripts {
            utxos.push(
                simplex::simplicityhl::simplicity::jet::elements::ElementsUtxo {
                    script_pubkey,
                    asset: Asset::default(),
                    value: Value::default(),
                },
            );
        }
        utxos.push(
            simplex::simplicityhl::simplicity::jet::elements::ElementsUtxo {
                script_pubkey: vote_script_pubkey,
                asset: Asset::default(),
                value: Value::default(),
            },
        );

        let env = ElementsEnv::new(
            tx,
            utxos,
            vote_input_index,
            cmr,
            ControlBlock::from_slice(&vote_control_block.serialize())?,
            None,
            BlockHash::all_zeros(),
        );

        let _ = run_program(
            &program,
            WitnessValues::default(),
            &env,
            TrackerLogLevel::Trace,
        )?;
        Ok(())
    }

    #[test]
    fn test_vote_accepts_expected_target_multisig_prefix_count() -> anyhow::Result<()> {
        let target_script = Script::from(vec![0x51]);

        run_vote_with_inputs(
            target_script.clone(),
            2,
            vec![target_script.clone(), target_script],
        )
    }

    #[test]
    fn test_vote_rejects_unexpected_target_multisig_prefix_count() -> anyhow::Result<()> {
        let target_script = Script::from(vec![0x51]);

        let result = run_vote_with_inputs(
            target_script.clone(),
            1,
            vec![target_script.clone(), target_script],
        );
        assert!(result.is_err());

        Ok(())
    }

    #[test]
    fn test_vote_rejects_target_after_non_target_input() -> anyhow::Result<()> {
        let target_script = Script::from(vec![0x51]);
        let other_script = Script::from(vec![0x52]);

        let result =
            run_vote_with_inputs(target_script.clone(), 1, vec![other_script, target_script]);
        assert!(result.is_err());

        Ok(())
    }
}
