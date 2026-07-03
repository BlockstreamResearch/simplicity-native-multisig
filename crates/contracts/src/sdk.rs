//! High-level helpers for constructing vote and multisig transactions.
//!
//! This module keeps protocol-level transaction assembly out of application and
//! test code. Callers still own funding, broadcasting, fee policy, and wallet
//! integration.

use std::sync::Arc;

use crate::common::{Utxo, multisig_input_prefix};
use crate::multisig::{MultisigBuilder, PARTICIPANT_COUNT, VoteEntry, witness_values};
use crate::vote::VoteBuilder;
use crate::vote::message::{base_message_and_input_count, participant_message};

use simplicityhl::elements::hashes::{Hash, sha256};
use simplicityhl::elements::pset::{Input, Output, PartiallySignedTransaction};
use simplicityhl::elements::schnorr::Keypair;
use simplicityhl::elements::secp256k1_zkp::schnorr::Signature;
use simplicityhl::elements::secp256k1_zkp::{Message, SECP256K1};
use simplicityhl::elements::taproot::ControlBlock;
use simplicityhl::elements::{BlockHash, Script, Transaction};
use simplicityhl::simplicity::jet::Elements;
use simplicityhl::simplicity::jet::elements::{ElementsEnv, ElementsUtxo};
use simplicityhl::simplicity::{BitMachine, Cmr, RedeemNode, Value as SimplicityValue};
use simplicityhl::{CompiledProgram, WitnessValues};

/// Prepared participant vote message for a proposed multisig spend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VotePlan {
    vote_builder: VoteBuilder,
    message: Message,
    message_hash: sha256::Hash,
}

impl VotePlan {
    /// Raw secp256k1 message to sign.
    #[must_use]
    pub const fn message(&self) -> Message {
        self.message
    }

    /// SHA256 participant message hash backing [`Self::message`].
    #[must_use]
    pub const fn message_hash(&self) -> sha256::Hash {
        self.message_hash
    }

    /// Sign this vote plan with a participant key.
    #[must_use]
    pub fn sign(&self, participant_key: &Keypair) -> SignedVote {
        self.signed_vote(SECP256K1.sign_schnorr(&self.message, participant_key))
    }

    /// Pair this vote plan with an externally produced participant signature.
    #[must_use]
    pub fn signed_vote(&self, signature: Signature) -> SignedVote {
        SignedVote {
            vote_builder: self.vote_builder.clone(),
            signature,
        }
    }
}

/// Participant signature plus the vote covenant builder it signs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedVote {
    vote_builder: VoteBuilder,
    signature: Signature,
}

impl SignedVote {
    /// Participant signature committed by the vote covenant.
    #[must_use]
    pub const fn signature(&self) -> Signature {
        self.signature
    }

    /// Script pubkey that locks funds to this participant vote.
    pub fn script_pubkey(&self) -> anyhow::Result<Script> {
        self.vote_builder.script_pubkey(self.signature)
    }

    fn entry(&self) -> anyhow::Result<VoteEntry> {
        Ok(VoteEntry {
            signature: self.signature,
            vote_executable_leaf_hash: self.vote_builder.executable_leaf_hash()?,
        })
    }
}

/// A signed vote and the UTXO that funds its covenant input.
#[derive(Debug, Clone)]
pub struct VoteInput {
    pub vote: SignedVote,
    pub utxo: Utxo,
}

/// Prepare the canonical participant vote message for a proposed transaction.
pub fn create_vote(
    multisig_builder: &MultisigBuilder,
    proposed_pst: &PartiallySignedTransaction,
    total_proposed_outputs: u16,
) -> anyhow::Result<VotePlan> {
    let proposed_tx = proposed_pst.extract_tx()?;
    let multisig_script = multisig_builder.script_pubkey()?;
    let (base_message, multisig_input_count) =
        base_message_and_input_count(&proposed_tx, &multisig_script, total_proposed_outputs)?;

    let vote_builder = VoteBuilder::new(multisig_script, multisig_input_count)?;
    let message_hash = participant_message(vote_builder.executable_leaf_hash()?, base_message);

    Ok(VotePlan {
        vote_builder,
        message: Message::from_digest(*message_hash.as_byte_array()),
        message_hash,
    })
}

/// Build a proposal PSET whose input prefix is marked as multisig-owned.
///
/// The marker is stored in `final_script_sig` so vote-message construction can
/// identify the multisig prefix before the final Taproot witnesses exist. The
/// marker is removed by [`finalize_multisig_spend`] before extraction.
#[must_use]
pub fn create_proposed_multisig_spend(
    multisig_script: &Script,
    multisig_utxos: &[Utxo],
    outputs: impl IntoIterator<Item = Output>,
) -> PartiallySignedTransaction {
    let mut pst = PartiallySignedTransaction::new_v2();

    for utxo in multisig_utxos {
        let mut input = Input::from_prevout(utxo.outpoint);
        input.final_script_sig = Some(multisig_script.clone());
        pst.add_input(input);
    }

    for output in outputs {
        pst.add_output(output);
    }

    pst
}

/// Finalize a multisig spend by appending vote inputs and building all covenant witnesses.
///
/// `proposed_input_utxos` must match the inputs already present in
/// `proposed_pst`, in order. Vote inputs are appended in participant order from
/// the `vote_inputs` slots.
pub fn finalize_multisig_spend(
    multisig_builder: &MultisigBuilder,
    proposed_pst: PartiallySignedTransaction,
    proposed_input_utxos: Vec<Utxo>,
    vote_inputs: &[Option<VoteInput>; PARTICIPANT_COUNT],
    total_proposed_outputs: u16,
    genesis_hash: BlockHash,
) -> anyhow::Result<PartiallySignedTransaction> {
    let (final_pst, input_utxos, multisig_input_count) = prepare_multisig_spend_inputs(
        multisig_builder,
        proposed_pst,
        proposed_input_utxos,
        vote_inputs,
    )?;
    finalize_prepared_multisig_spend(
        multisig_builder,
        final_pst,
        &input_utxos,
        vote_inputs,
        multisig_input_count,
        total_proposed_outputs,
        genesis_hash,
    )
}

/// Insert vote inputs into the final input order without constructing covenant witnesses.
pub fn prepare_multisig_spend_inputs(
    multisig_builder: &MultisigBuilder,
    proposed_pst: PartiallySignedTransaction,
    proposed_input_utxos: Vec<Utxo>,
    vote_inputs: &[Option<VoteInput>; PARTICIPANT_COUNT],
) -> anyhow::Result<(PartiallySignedTransaction, Vec<Utxo>, usize)> {
    if proposed_pst.inputs().len() != proposed_input_utxos.len() {
        anyhow::bail!("proposed input UTXO count does not match proposal inputs");
    }

    let multisig_script = multisig_builder.script_pubkey()?;
    let proposed_tx = proposed_pst.extract_tx()?;
    let multisig_input_count = multisig_input_prefix(&proposed_tx, &multisig_script).count();
    if multisig_input_count == 0 {
        anyhow::bail!("at least one multisig input is required");
    }

    let mut final_pst = proposed_pst;
    let mut input_utxos = proposed_input_utxos;
    for (vote_input_index, vote_input) in (multisig_input_count..).zip(vote_inputs.iter().flatten())
    {
        final_pst.insert_input(
            Input::from_prevout(vote_input.utxo.outpoint),
            vote_input_index,
        );
        input_utxos.insert(vote_input_index, vote_input.utxo.clone());
    }

    for (input, utxo) in final_pst.inputs_mut().iter_mut().zip(input_utxos.iter()) {
        attach_input_utxo(input, utxo);
    }

    Ok((final_pst, input_utxos, multisig_input_count))
}

/// Add covenant witnesses to a PSET whose final transaction shape is already fixed.
pub fn finalize_prepared_multisig_spend(
    multisig_builder: &MultisigBuilder,
    mut final_pst: PartiallySignedTransaction,
    input_utxos: &[Utxo],
    vote_inputs: &[Option<VoteInput>; PARTICIPANT_COUNT],
    multisig_input_count: usize,
    total_proposed_outputs: u16,
    genesis_hash: BlockHash,
) -> anyhow::Result<PartiallySignedTransaction> {
    if final_pst.inputs().len() != input_utxos.len() {
        anyhow::bail!("prepared input UTXO count does not match PSET inputs");
    }

    if multisig_input_count == 0 {
        anyhow::bail!("at least one multisig input is required");
    }

    let compiled_multisig = multisig_builder.compiled()?;
    let multisig_script = compiled_multisig.script_pubkey();
    for (index, utxo) in input_utxos.iter().take(multisig_input_count).enumerate() {
        if utxo.txout.script_pubkey != multisig_script {
            anyhow::bail!("input UTXO {index} is not locked to the multisig script");
        }
    }

    let vote_count = vote_inputs.iter().flatten().count();
    if vote_count < usize::try_from(multisig_builder.threshold())? {
        anyhow::bail!("not enough vote inputs to satisfy multisig threshold");
    }

    let mut vote_entries = [None; PARTICIPANT_COUNT];
    let mut appended_votes = Vec::new();
    let vote_slots = vote_inputs
        .iter()
        .enumerate()
        .filter_map(|(slot, vote_input)| vote_input.as_ref().map(|vote_input| (slot, vote_input)));
    for (vote_input_index, (slot, vote_input)) in (multisig_input_count..).zip(vote_slots) {
        vote_entries[slot] = Some(vote_input.vote.entry()?);
        appended_votes.push((vote_input_index, vote_input));
    }

    for input in final_pst.inputs_mut().iter_mut().take(multisig_input_count) {
        input.final_script_sig = None;
    }
    for (input, utxo) in final_pst.inputs_mut().iter_mut().zip(input_utxos.iter()) {
        attach_input_utxo(input, utxo);
    }

    let final_tx = final_pst.extract_tx()?;
    let multisig_control_block = compiled_multisig.control_block()?;

    for input_index in 0..multisig_input_count {
        let env = elements_env(
            &final_tx,
            input_utxos,
            input_index,
            compiled_multisig.cmr(),
            multisig_control_block.clone(),
            genesis_hash,
        )?;
        let witness = final_script_witness(
            compiled_multisig.program(),
            witness_values(&vote_entries, total_proposed_outputs),
            &env,
            &multisig_control_block,
        )?;
        final_pst.inputs_mut()[input_index].final_script_witness = Some(witness);
    }

    for (input_index, vote_input) in appended_votes {
        let compiled_vote = vote_input.vote.vote_builder.compiled()?;
        let control_block = compiled_vote.control_block(vote_input.vote.signature)?;
        let env = elements_env(
            &final_tx,
            input_utxos,
            input_index,
            compiled_vote.cmr(),
            control_block.clone(),
            genesis_hash,
        )?;
        let witness = final_script_witness(
            compiled_vote.program(),
            WitnessValues::default(),
            &env,
            &control_block,
        )?;
        final_pst.inputs_mut()[input_index].final_script_witness = Some(witness);
    }

    Ok(final_pst)
}

fn attach_input_utxo(input: &mut Input, utxo: &Utxo) {
    input.witness_utxo = Some(utxo.txout.clone());
    if let Some(secrets) = utxo.secrets {
        input.amount = Some(secrets.value);
        input.asset = Some(secrets.asset);
        return;
    }
    if let Some(amount) = utxo.txout.value.explicit() {
        input.amount = Some(amount);
    }
    if let Some(asset) = utxo.txout.asset.explicit() {
        input.asset = Some(asset);
    }
}

fn elements_env(
    tx: &Transaction,
    input_utxos: &[Utxo],
    input_index: usize,
    cmr: Cmr,
    control_block: ControlBlock,
    genesis_hash: BlockHash,
) -> anyhow::Result<ElementsEnv<Arc<Transaction>>> {
    Ok(ElementsEnv::new(
        Arc::new(tx.clone()),
        input_utxos
            .iter()
            .map(|utxo| ElementsUtxo {
                script_pubkey: utxo.txout.script_pubkey.clone(),
                asset: utxo.txout.asset,
                value: utxo.txout.value,
            })
            .collect(),
        u32::try_from(input_index)?,
        cmr,
        control_block,
        None,
        genesis_hash,
    ))
}

fn final_script_witness(
    program: &CompiledProgram,
    witness_values: WitnessValues,
    env: &ElementsEnv<Arc<Transaction>>,
    control_block: &ControlBlock,
) -> anyhow::Result<Vec<Vec<u8>>> {
    let satisfied = program
        .satisfy(witness_values)
        .map_err(|e| anyhow::anyhow!(e))?;
    let pruned: Arc<RedeemNode<Elements>> = satisfied
        .redeem()
        .prune(env)
        .map_err(|e| anyhow::anyhow!(e))?;
    let mut mac = BitMachine::for_program(&pruned)?;
    let _: SimplicityValue = mac.exec(&pruned, env).map_err(|e| anyhow::anyhow!(e))?;

    let (program_bytes, witness_bytes) = pruned.to_vec_with_witness();

    Ok(vec![
        witness_bytes,
        program_bytes,
        pruned.cmr().as_ref().to_vec(),
        control_block.serialize(),
    ])
}
