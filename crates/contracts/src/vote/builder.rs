//! Builder for the vote covenant.
//!
//! A vote is a signature commitment with executable prechecks.  The executable
//! leaf is `vote.simf`; the hidden state leaf is `TapData(SHA256(signature))`.
//! `multisig_n_of_3.simf` recomputes that tap tree from witness data and checks
//! that the corresponding vote input is present.

use std::collections::HashMap;

use crate::common::{script_hash, script_ver, unspendable_internal_key};
use simplicityhl::elements::Script;
use simplicityhl::elements::bitcoin::secp256k1;
use simplicityhl::elements::hashes::{Hash, HashEngine, sha256};
use simplicityhl::elements::secp256k1_zkp::schnorr::Signature;
use simplicityhl::elements::taproot::{
    ControlBlock, TapLeafHash, TaprootBuilder, TaprootSpendInfo,
};
use simplicityhl::num::U256;
use simplicityhl::simplicity::Cmr;
use simplicityhl::str::WitnessName;
use simplicityhl::value::UIntValue;
use simplicityhl::{Arguments, CompiledProgram, TemplateProgram};

/// Source of the vote covenant program.
const VOTE_SOURCE: &str = include_str!("../../simf/vote.simf");

/// Static parameters compiled into `vote.simf`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct VoteParameters {
    target_multisig_script_pubkey: Script,
    expected_multisig_inputs_count: u32,
}

impl VoteParameters {
    fn new(
        target_multisig_script_pubkey: Script,
        expected_multisig_inputs_count: u32,
    ) -> anyhow::Result<Self> {
        if expected_multisig_inputs_count == 0 {
            anyhow::bail!("expected multisig inputs count must be greater than zero");
        }

        Ok(Self {
            target_multisig_script_pubkey,
            expected_multisig_inputs_count,
        })
    }

    fn arguments(&self) -> Arguments {
        Arguments::from(HashMap::from([
            (
                WitnessName::from_str_unchecked("TARGET_MULTISIG"),
                simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
                    script_hash(&self.target_multisig_script_pubkey).to_byte_array(),
                ))),
            ),
            (
                WitnessName::from_str_unchecked("EXPECTED_MULTISIG_INPUTS_COUNT"),
                simplicityhl::Value::from(UIntValue::U32(self.expected_multisig_inputs_count)),
            ),
        ]))
    }
}

/// High-level builder for compiling and addressing a vote covenant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VoteBuilder {
    parameters: VoteParameters,
}

/// A vote covenant compiled once, with its Taproot commitment data.
///
/// The vote tap tree pairs the executable leaf with a hidden state leaf that
/// commits to the participant signature, so spend info is derived per
/// signature. Compiling the Simplicity template is comparatively expensive:
/// callers that need more than one of program, CMR, leaf hash, script pubkey,
/// or control block should go through [`VoteBuilder::compiled`] instead of the
/// per-value accessors.
#[derive(Debug)]
pub struct CompiledVote {
    program: CompiledProgram,
    cmr: Cmr,
}

impl CompiledVote {
    #[must_use]
    pub const fn program(&self) -> &CompiledProgram {
        &self.program
    }

    /// Commitment Merkle root of the compiled vote executable leaf.
    #[must_use]
    pub const fn cmr(&self) -> Cmr {
        self.cmr
    }

    /// Tapleaf hash of the executable vote leaf.
    #[must_use]
    pub fn executable_leaf_hash(&self) -> TapLeafHash {
        let (script, version) = script_ver(self.cmr);
        TapLeafHash::from_script(&script, version)
    }

    fn taproot_spend_info(
        &self,
        participant_signature: Signature,
    ) -> anyhow::Result<TaprootSpendInfo> {
        let (script, version) = script_ver(self.cmr);
        let signature_hash = sha256::Hash::hash(&participant_signature.serialize());
        let tap_data_tag = sha256::Hash::hash(b"TapData");
        let mut tap_data_engine = sha256::Hash::engine();
        tap_data_engine.input(tap_data_tag.as_byte_array());
        tap_data_engine.input(tap_data_tag.as_byte_array());
        tap_data_engine.input(signature_hash.as_byte_array());
        let state_hash = sha256::Hash::from_engine(tap_data_engine);

        let builder = TaprootBuilder::new()
            .add_leaf_with_ver(1, script, version)
            .map_err(anyhow::Error::msg)?
            .add_hidden(1, state_hash)
            .map_err(anyhow::Error::msg)?;

        builder
            .finalize(secp256k1::SECP256K1, unspendable_internal_key())
            .map_err(anyhow::Error::msg)
    }

    /// Control block for spending the executable vote leaf.
    pub fn control_block(&self, participant_signature: Signature) -> anyhow::Result<ControlBlock> {
        self.taproot_spend_info(participant_signature)?
            .control_block(&script_ver(self.cmr))
            .ok_or_else(|| anyhow::anyhow!("missing vote control block"))
    }

    /// Script pubkey that locks funds to this signature-bearing vote.
    pub fn script_pubkey(&self, participant_signature: Signature) -> anyhow::Result<Script> {
        Ok(Script::new_v1_p2tr_tweaked(
            self.taproot_spend_info(participant_signature)?.output_key(),
        ))
    }
}

impl VoteBuilder {
    /// Validate that the expected multisig input count is non-zero.
    pub fn new(
        target_multisig_script_pubkey: Script,
        expected_multisig_inputs_count: u32,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            parameters: VoteParameters::new(
                target_multisig_script_pubkey,
                expected_multisig_inputs_count,
            )?,
        })
    }

    /// Compile the vote covenant.
    pub fn compile(&self) -> anyhow::Result<CompiledProgram> {
        let template_program = TemplateProgram::new(VOTE_SOURCE).map_err(anyhow::Error::msg)?;

        template_program
            .instantiate(self.parameters.arguments(), false)
            .map_err(anyhow::Error::msg)
    }

    /// Compile the vote covenant and derive its commitment data once.
    pub fn compiled(&self) -> anyhow::Result<CompiledVote> {
        let program = self.compile()?;
        let cmr = program.commit().cmr();

        Ok(CompiledVote { program, cmr })
    }

    /// Tapleaf hash of the executable vote leaf.
    pub fn executable_leaf_hash(&self) -> anyhow::Result<TapLeafHash> {
        Ok(self.compiled()?.executable_leaf_hash())
    }

    /// Script pubkey that locks funds to this signature-bearing vote.
    pub fn script_pubkey(&self, participant_signature: Signature) -> anyhow::Result<Script> {
        self.compiled()?.script_pubkey(participant_signature)
    }
}
