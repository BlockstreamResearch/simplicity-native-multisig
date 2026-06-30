use anyhow::Context;
use simplex::simplicityhl::elements::Script;
use simplex::simplicityhl::elements::pset::PartiallySignedTransaction;
use simplex::simplicityhl::elements::schnorr::Keypair;
use simplex::simplicityhl::elements::secp256k1_zkp::rand::thread_rng;
use simplex::simplicityhl::elements::secp256k1_zkp::{SECP256K1, SecretKey};
use simplicity_native_multisig_contracts::common::Utxo;
use simplicity_native_multisig_contracts::multisig::{MultisigBuilder, PARTICIPANT_COUNT};
use simplicity_native_multisig_contracts::sdk::{SignedVote, create_vote};

pub struct Setup {
    participants_private_keys: [Keypair; PARTICIPANT_COUNT],
    pub(crate) multisig_builder: MultisigBuilder,
}

fn keypair() -> Keypair {
    Keypair::from_secret_key(SECP256K1, &SecretKey::new(&mut thread_rng()))
}

pub fn fund_script(
    context: &simplex::TestContext,
    script: &Script,
    amount: u64,
) -> anyhow::Result<Utxo> {
    let signer = context.get_default_signer();
    let provider = context.get_default_provider();
    let receipt = signer.send(script.clone(), amount)?;
    receipt.wait()?;
    let txid = receipt.txid();

    let utxo = provider
        .fetch_scripthash_utxos(script)?
        .into_iter()
        .find(|utxo| utxo.outpoint.txid == txid && utxo.amount() == amount)
        .with_context(|| format!("missing funded UTXO {txid}:{amount}"))?;

    Ok(Utxo {
        outpoint: utxo.outpoint,
        txout: utxo.txout,
        secrets: utxo.secrets,
    })
}

impl Setup {
    /// Build a deterministic test setup with a fresh participant set.
    ///
    /// # Errors
    ///
    /// Returns an error if the multisig builder rejects the requested threshold.
    pub(crate) fn new(threshold: u32) -> anyhow::Result<Self> {
        let participants_private_keys = [keypair(), keypair(), keypair()];

        Ok(Self {
            participants_private_keys,
            multisig_builder: MultisigBuilder::new(
                threshold,
                [
                    participants_private_keys[0].x_only_public_key().0,
                    participants_private_keys[1].x_only_public_key().0,
                    participants_private_keys[2].x_only_public_key().0,
                ],
            )?,
        })
    }

    /// Create a signed vote for a proposed spend from one participant.
    ///
    /// # Errors
    ///
    /// Returns an error if vote construction fails or `participant_id` is out of bounds.
    pub(crate) fn vote_by(
        &self,
        proposed_pst: &PartiallySignedTransaction,
        total_proposed_outputs: u16,
        participant_id: u32,
    ) -> anyhow::Result<SignedVote> {
        let vote_plan = create_vote(&self.multisig_builder, proposed_pst, total_proposed_outputs)?;
        let signer = self
            .participants_private_keys
            .get(participant_id as usize)
            .ok_or_else(|| anyhow::anyhow!("index out of bounds"))?;

        Ok(vote_plan.sign(signer))
    }
}
