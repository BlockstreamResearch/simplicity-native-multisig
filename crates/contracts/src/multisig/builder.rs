//! Builder for the native multisig n of 3 covenant.

use crate::common::{script_ver, unspendable_internal_key};

use std::collections::HashMap;

use simplicityhl::elements::Script;
use simplicityhl::elements::bitcoin::secp256k1;
use simplicityhl::elements::hashes::Hash;
use simplicityhl::elements::schnorr::XOnlyPublicKey;
use simplicityhl::elements::secp256k1_zkp::schnorr::Signature;
use simplicityhl::elements::taproot::{
    ControlBlock, TapLeafHash, TaprootBuilder, TaprootSpendInfo,
};
use simplicityhl::num::U256;
use simplicityhl::simplicity::Cmr;
use simplicityhl::str::WitnessName;
use simplicityhl::types::TypeConstructible;
use simplicityhl::value::{UIntValue, ValueConstructible};
use simplicityhl::{Arguments, CompiledProgram, ResolvedType, TemplateProgram, WitnessValues};

pub const PARTICIPANT_COUNT: usize = 3;

const MULTISIG_SOURCE: &str = include_str!("../../simf/multisig_n_of_3.simf");

/// Multisig arguments required for the compilation of the covenant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MultisigParameters {
    threshold: u32,
    participants: [XOnlyPublicKey; PARTICIPANT_COUNT],
}

impl MultisigParameters {
    fn new(
        threshold: u32,
        participants: [XOnlyPublicKey; PARTICIPANT_COUNT],
    ) -> anyhow::Result<Self> {
        let threshold_usize = usize::try_from(threshold)?;
        if !(1..=PARTICIPANT_COUNT).contains(&threshold_usize) {
            anyhow::bail!("invalid threshold value: {threshold}")
        }
        for left in 0..PARTICIPANT_COUNT {
            for right in left + 1..PARTICIPANT_COUNT {
                if participants[left] == participants[right] {
                    anyhow::bail!("participants must be distinct")
                }
            }
        }

        Ok(Self {
            threshold,
            participants,
        })
    }

    const fn threshold(&self) -> u32 {
        self.threshold
    }

    const fn participants(&self) -> [XOnlyPublicKey; PARTICIPANT_COUNT] {
        self.participants
    }

    fn arguments(&self) -> Arguments {
        let participants: Vec<_> = self
            .participants
            .iter()
            .map(|pubkey| {
                simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
                    pubkey.serialize(),
                )))
            })
            .collect();

        Arguments::from(HashMap::from([
            (
                WitnessName::from_str_unchecked("THRESHOLD"),
                simplicityhl::Value::from(UIntValue::U32(self.threshold)),
            ),
            (
                WitnessName::from_str_unchecked("PARTICIPANTS"),
                simplicityhl::Value::array(participants, ResolvedType::u256()),
            ),
        ]))
    }
}

/// A vote witness entry for one declared participant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VoteEntry {
    /// Participant signature over `SHA256(vote_executable_leaf_hash || base_message)`.
    pub(crate) signature: Signature,
    /// Tapleaf hash of the executable `vote.simf` leaf that committed the signature.
    pub(crate) vote_executable_leaf_hash: TapLeafHash,
}

/// High-level builder for compiling and addressing a multisig covenant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MultisigBuilder {
    parameters: MultisigParameters,
}

mod certificate;
mod coq;
mod coq_typed;
mod coq_typed_text;
mod coq_types;
mod encoding;

pub use self::certificate::{CompiledMultisigCertificate, CompiledMultisigCertificateArtifact};
pub use self::coq_typed::CoqModuleFile;

use self::encoding::encoded_type_table;

/// A multisig covenant compiled once, with its Taproot commitment data.
///
/// Compiling the Simplicity template is comparatively expensive, so callers
/// that need more than one of program, CMR, script pubkey, or control block
/// should go through [`MultisigBuilder::compiled`] instead of the per-value
/// accessors.
#[derive(Debug)]
pub struct CompiledMultisig {
    program: CompiledProgram,
    cmr: Cmr,
    spend_info: TaprootSpendInfo,
}

impl CompiledMultisig {
    #[must_use]
    pub const fn program(&self) -> &CompiledProgram {
        &self.program
    }

    /// Commitment Merkle root of the compiled program.
    #[must_use]
    pub const fn cmr(&self) -> Cmr {
        self.cmr
    }

    /// Control block for spending the executable multisig leaf.
    pub fn control_block(&self) -> anyhow::Result<ControlBlock> {
        self.spend_info
            .control_block(&script_ver(self.cmr))
            .ok_or_else(|| anyhow::anyhow!("missing multisig control block"))
    }

    /// Script pubkey that locks funds to this multisig covenant.
    #[must_use]
    pub fn script_pubkey(&self) -> Script {
        Script::new_v1_p2tr_tweaked(self.spend_info.output_key())
    }
}

impl MultisigBuilder {
    /// Validate the threshold range and participant distinctness.
    pub fn new(
        threshold: u32,
        participants: [XOnlyPublicKey; PARTICIPANT_COUNT],
    ) -> anyhow::Result<Self> {
        Ok(Self {
            parameters: MultisigParameters::new(threshold, participants)?,
        })
    }

    pub(crate) const fn threshold(&self) -> u32 {
        self.parameters.threshold()
    }

    /// Compile the covenant program with the configured parameters.
    pub fn compile(&self) -> anyhow::Result<CompiledProgram> {
        let template_program = TemplateProgram::new(MULTISIG_SOURCE).map_err(anyhow::Error::msg)?;

        template_program
            .instantiate(self.parameters.arguments(), false)
            .map_err(anyhow::Error::msg)
    }

    /// Compile the covenant and derive its Taproot commitment data once.
    pub fn compiled(&self) -> anyhow::Result<CompiledMultisig> {
        let program = self.compile()?;
        let cmr = program.commit().cmr();
        let (script, version) = script_ver(cmr);
        let spend_info = TaprootBuilder::new()
            .add_leaf_with_ver(0, script, version)
            .map_err(anyhow::Error::msg)?
            .finalize(secp256k1::SECP256K1, unspendable_internal_key())
            .map_err(anyhow::Error::msg)?;

        Ok(CompiledMultisig {
            program,
            cmr,
            spend_info,
        })
    }

    /// Commitment Merkle root of the compiled program.
    pub fn cmr(&self) -> anyhow::Result<Cmr> {
        Ok(self.compile()?.commit().cmr())
    }

    /// Export the committed multisig artifact that the formal byte bridge checks.
    pub fn compiled_certificate(&self) -> anyhow::Result<CompiledMultisigCertificate> {
        let commit = self.compile()?.commit();

        Ok(CompiledMultisigCertificate {
            parameters: self.parameters,
            cmr: commit.cmr(),
            program_bytes: commit.to_vec_without_witness(),
            type_table: encoded_type_table(&commit),
            root_arrow: commit.arrow().shallow_clone(),
        })
    }

    /// Control block for spending the executable multisig leaf.
    pub fn control_block(&self) -> anyhow::Result<ControlBlock> {
        self.compiled()?.control_block()
    }

    /// Script pubkey that locks funds to this multisig covenant.
    pub fn script_pubkey(&self) -> anyhow::Result<Script> {
        Ok(self.compiled()?.script_pubkey())
    }
}

/// Build the multisig witness expected by `multisig_n_of_3.simf`.
///
/// Vote slots must follow participant declaration order.  Missing participant
/// votes are represented by `None`, even when the threshold is lower than the
/// participant count.
#[must_use]
pub fn witness_values(
    votes: &[Option<VoteEntry>; PARTICIPANT_COUNT],
    total_proposed_outputs: u16,
) -> WitnessValues {
    let payload_type =
        TypeConstructible::product(ResolvedType::byte_array(64), ResolvedType::u256());

    let votes: Vec<_> = votes
        .iter()
        .copied()
        .map(|vote| {
            vote.map_or_else(
                || simplicityhl::Value::none(payload_type.clone()),
                |vote| {
                    simplicityhl::Value::some(simplicityhl::Value::tuple([
                        simplicityhl::Value::byte_array(vote.signature.serialize()),
                        simplicityhl::Value::from(UIntValue::U256(U256::from_byte_array(
                            *vote.vote_executable_leaf_hash.as_byte_array(),
                        ))),
                    ]))
                },
            )
        })
        .collect();

    WitnessValues::from(HashMap::from([
        (
            WitnessName::from_str_unchecked("VOTES"),
            simplicityhl::Value::array(votes, ResolvedType::option(payload_type)),
        ),
        (
            WitnessName::from_str_unchecked("TOTAL_PROPOSED_OUTPUTS"),
            simplicityhl::Value::from(UIntValue::U16(total_proposed_outputs)),
        ),
    ]))
}

#[cfg(test)]
mod tests;
