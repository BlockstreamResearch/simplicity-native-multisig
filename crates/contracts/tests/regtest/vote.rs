use crate::common::setup::{Setup, fund_script};

use simplex::simplicityhl::elements::confidential;
use simplex::simplicityhl::elements::pset::Output;
use simplex::transaction::{FinalTransaction, PartialOutput};
use simplicity_native_multisig_contracts::sdk::{create_proposed_multisig_spend, create_vote};
use simplicity_native_multisig_contracts::vote::onchain_encoder;

#[simplex::test]
fn create_vote_with_tx_context(context: simplex::TestContext) -> anyhow::Result<()> {
    let setup = Setup::new(1)?;

    let signer = context.get_default_signer();
    let provider = context.get_default_provider();
    let policy_asset = context.get_network().policy_asset();
    let multisig_script = setup.multisig_builder.script_pubkey()?;

    let multisig_utxo = fund_script(&context, &multisig_script, 2_000)?;

    let proposed_pst = create_proposed_multisig_spend(
        &multisig_script,
        std::slice::from_ref(&multisig_utxo),
        [Output::new_explicit(
            signer.get_address().script_pubkey(),
            1_500,
            policy_asset,
            None,
        )],
    );

    let total_proposed_outputs = 1;
    let expected_vote_plan = create_vote(
        &setup.multisig_builder,
        &proposed_pst,
        total_proposed_outputs,
    )?;
    let signed_vote = setup.vote_by(&proposed_pst, total_proposed_outputs, 0)?;
    let vote_script = signed_vote.script_pubkey()?;

    let mut vote_transaction = FinalTransaction::new();
    vote_transaction.add_output(PartialOutput::new(vote_script, 1_000, policy_asset));
    for output in onchain_encoder::encode(&proposed_pst, signed_vote.signature())? {
        let txout = output.to_txout();
        let confidential::Asset::Explicit(asset) = txout.asset else {
            anyhow::bail!("encoded output asset must be explicit");
        };
        let confidential::Value::Explicit(amount) = txout.value else {
            anyhow::bail!("encoded output amount must be explicit");
        };

        vote_transaction.add_output(PartialOutput::new(txout.script_pubkey, amount, asset));
    }

    let vote_receipt = signer.broadcast(&vote_transaction)?;
    vote_receipt.wait()?;

    let fetched_vote_tx = provider.fetch_transaction(&vote_receipt.txid())?;
    let decoded_vote = onchain_encoder::decode(&fetched_vote_tx)?;
    let decoded_vote_plan = create_vote(
        &setup.multisig_builder,
        &decoded_vote.proposed_pst,
        total_proposed_outputs,
    )?;

    assert_eq!(
        expected_vote_plan.message_hash(),
        decoded_vote_plan.message_hash()
    );
    assert_eq!(signed_vote.signature(), decoded_vote.participant_signature);

    Ok(())
}
