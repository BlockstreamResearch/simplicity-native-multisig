use std::collections::HashMap;

use crate::constants::unspendable_internal_key;
use crate::scripts::script_ver;
use simplex::simplicityhl::elements::bitcoin::secp256k1;
use simplex::simplicityhl::elements::schnorr::XOnlyPublicKey;
use simplex::simplicityhl::elements::taproot::TaprootBuilder;
use simplex::simplicityhl::num::U256;
use simplex::simplicityhl::simplicity::Cmr;
use simplex::simplicityhl::str::WitnessName;
use simplex::simplicityhl::types::TypeConstructible;
use simplex::simplicityhl::value::{UIntValue, ValueConstructible};
use simplex::simplicityhl::{Arguments, CompiledProgram, TemplateProgram};

pub const MULTISIG_SOURCE: &str = include_str!("../simf/multisig_n_of_3.simf");

fn get_multisig_program(
    threshold: u32,
    participants: [XOnlyPublicKey; 3],
    is_debug_symbols_enabled: bool,
) -> anyhow::Result<CompiledProgram> {
    let template_program = TemplateProgram::new(MULTISIG_SOURCE).map_err(|e| anyhow::anyhow!(e))?;

    let participants: Vec<simplex::simplicityhl::Value> = participants
        .iter()
        .map(|pubkey| {
            simplex::simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
                pubkey.serialize(),
            )))
        })
        .collect();

    let args = Arguments::from(HashMap::from([
        (
            WitnessName::from_str_unchecked("THRESHOLD"),
            simplex::simplicityhl::Value::from(UIntValue::U32(threshold)),
        ),
        (
            WitnessName::from_str_unchecked("PARTICIPANTS"),
            simplex::simplicityhl::Value::array(
                participants,
                simplex::simplicityhl::types::ResolvedType::u256(),
            ),
        ),
    ]));

    template_program
        .instantiate(args, is_debug_symbols_enabled)
        .map_err(|e| anyhow::anyhow!(e))
}

fn taproot_spend_info(
    cmr: Cmr,
) -> anyhow::Result<simplex::simplicityhl::elements::taproot::TaprootSpendInfo> {
    let (script, version) = script_ver(cmr);

    let builder = TaprootBuilder::new()
        .add_leaf_with_ver(0, script, version)
        .map_err(|e| anyhow::anyhow!(e))?;

    builder
        .finalize(secp256k1::SECP256K1, unspendable_internal_key())
        .map_err(|e| anyhow::anyhow!(e))
}

#[cfg(test)]
mod test {
    use crate::multisig_builder::get_multisig_program;
    use crate::runner::run_program;
    use crate::scripts::script_ver;
    use crate::vote_builder::{get_vote_program, taproot_spend_info as vote_taproot_spend_info};
    use std::collections::HashMap;

    use std::sync::Arc;

    use simplex::program::TrackerLogLevel;
    use simplex::simplicityhl::ResolvedType;
    use simplex::simplicityhl::elements::confidential::{Asset, Value};
    use simplex::simplicityhl::elements::encode;
    use simplex::simplicityhl::elements::hashes::{Hash, HashEngine, sha256};
    use simplex::simplicityhl::elements::pset::{Input, Output, PartiallySignedTransaction};
    use simplex::simplicityhl::elements::schnorr::Keypair;
    use simplex::simplicityhl::elements::secp256k1_zkp::rand::thread_rng;
    use simplex::simplicityhl::elements::secp256k1_zkp::{Message, SECP256K1, SecretKey};
    use simplex::simplicityhl::elements::taproot::{ControlBlock, TapLeafHash};
    use simplex::simplicityhl::elements::{
        AssetId, BlockHash, OutPoint, Script, Transaction, Txid,
    };
    use simplex::simplicityhl::num::U256;
    use simplex::simplicityhl::simplicity::jet::elements::ElementsEnv;
    use simplex::simplicityhl::str::WitnessName;
    use simplex::simplicityhl::types::TypeConstructible;
    use simplex::simplicityhl::value::{UIntValue, ValueConstructible};

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

    fn outputs_hash(tx: &Transaction) -> sha256::Hash {
        let mut output_asset_amounts_hash = sha256::Hash::engine();
        let mut output_nonces_hash = sha256::Hash::engine();
        let mut output_scripts_hash = sha256::Hash::engine();
        let mut output_range_proofs_hash = sha256::Hash::engine();

        for output in &tx.output {
            input_confidential(
                &mut output_asset_amounts_hash,
                &encode::serialize(&output.asset),
                0x0a,
                0x0b,
            );
            input_confidential(
                &mut output_asset_amounts_hash,
                &encode::serialize(&output.value),
                0x08,
                0x09,
            );
            input_confidential(
                &mut output_nonces_hash,
                &encode::serialize(&output.nonce),
                0x02,
                0x03,
            );

            input_hash(
                &mut output_scripts_hash,
                &sha256::Hash::hash(output.script_pubkey.as_bytes()),
            );

            let range_proof = output
                .witness
                .rangeproof
                .as_ref()
                .map(|proof| proof.serialize())
                .unwrap_or_default();
            input_hash(
                &mut output_range_proofs_hash,
                &sha256::Hash::hash(&range_proof),
            );
        }

        let mut outputs_hash = sha256::Hash::engine();
        input_hash(
            &mut outputs_hash,
            &sha256::Hash::from_engine(output_asset_amounts_hash),
        );
        input_hash(
            &mut outputs_hash,
            &sha256::Hash::from_engine(output_nonces_hash),
        );
        input_hash(
            &mut outputs_hash,
            &sha256::Hash::from_engine(output_scripts_hash),
        );
        input_hash(
            &mut outputs_hash,
            &sha256::Hash::from_engine(output_range_proofs_hash),
        );

        sha256::Hash::from_engine(outputs_hash)
    }

    #[test]
    fn test_multisig_spend_1_of_3() -> anyhow::Result<()> {
        let alice = Keypair::from_secret_key(&SECP256K1, &SecretKey::new(&mut thread_rng()));
        let bob = Keypair::from_secret_key(&SECP256K1, &SecretKey::new(&mut thread_rng()));
        let carol = Keypair::from_secret_key(&SECP256K1, &SecretKey::new(&mut thread_rng()));

        let program = get_multisig_program(
            1,
            [
                alice.x_only_public_key().0,
                bob.x_only_public_key().0,
                carol.x_only_public_key().0,
            ],
            true,
        )?;
        let cmr = program.commit().cmr();

        let spend_info = super::taproot_spend_info(cmr)?;
        let script_pubkey = Script::new_v1_p2tr_tweaked(spend_info.output_key());
        let (multisig_script, _) = script_ver(cmr);
        let vote_program = get_vote_program(multisig_script, true)?;
        let vote_cmr = vote_program.commit().cmr();
        let (vote_script, vote_version) = script_ver(vote_cmr);
        let vote_leaf_hash = TapLeafHash::from_script(&vote_script, vote_version);

        // Build transaction
        let mut pst = PartiallySignedTransaction::new_v2();
        let outpoint0 = OutPoint::new(Txid::from_slice(&[0; 32])?, 0);
        let outpoint1 = OutPoint::new(Txid::from_slice(&[1; 32])?, 0);
        pst.add_input(Input::from_prevout(outpoint0));
        pst.add_input(Input::from_prevout(outpoint1));
        pst.add_output(Output::new_explicit(
            Script::new(),
            0,
            AssetId::default(),
            None,
        ));

        let control_block = spend_info
            .control_block(&script_ver(cmr))
            .expect("Must retrieve control block for the script path");

        let tx = Arc::new(pst.extract_tx()?);

        let message = Message::from_digest(outputs_hash(&tx).to_byte_array());
        let alice_signature = alice.sign_schnorr(message);
        let vote_spend_info = vote_taproot_spend_info(alice_signature, vote_cmr)?;
        let vote_script_pubkey = Script::new_v1_p2tr_tweaked(vote_spend_info.output_key());

        // Set up environment
        let env = ElementsEnv::new(
            tx,
            vec![
                simplex::simplicityhl::simplicity::jet::elements::ElementsUtxo {
                    script_pubkey,
                    asset: Asset::default(),
                    value: Value::default(),
                },
                simplex::simplicityhl::simplicity::jet::elements::ElementsUtxo {
                    script_pubkey: vote_script_pubkey,
                    asset: Asset::default(),
                    value: Value::default(),
                },
            ],
            0,
            cmr,
            ControlBlock::from_slice(&control_block.serialize())?,
            None,
            BlockHash::all_zeros(),
        );

        let vote_payload_type =
            TypeConstructible::product(ResolvedType::byte_array(64), ResolvedType::u256());
        let empty_vote = || simplex::simplicityhl::Value::none(vote_payload_type.clone());
        let alice_vote = simplex::simplicityhl::Value::some(simplex::simplicityhl::Value::tuple([
            simplex::simplicityhl::Value::byte_array(alice_signature.serialize()),
            simplex::simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
                vote_leaf_hash.to_byte_array(),
            ))),
        ]));

        let votes = vec![alice_vote, empty_vote(), empty_vote()];

        let witness = simplex::simplicityhl::WitnessValues::from(HashMap::from([(
            WitnessName::from_str_unchecked("VOTES"),
            simplex::simplicityhl::Value::array(votes, ResolvedType::option(vote_payload_type)),
        )]));

        let _ = run_program(&program, witness, &env, TrackerLogLevel::Trace)?;

        Ok(())
    }
}
