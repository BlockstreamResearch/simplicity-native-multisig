use crate::common::setup::{Setup, fund_script};

use simplex::simplicityhl::elements::pset::Output;
use simplex::simplicityhl::elements::{Script, Transaction};
use simplicity_native_multisig_contracts::sdk::{
    VoteInput, create_proposed_multisig_spend, finalize_multisig_spend,
};

#[simplex::test]
fn create_multisig(context: simplex::TestContext) -> anyhow::Result<()> {
    let setup = Setup::new(1)?;

    let script_pubkey = setup.multisig_builder.script_pubkey()?;
    let signer = context.get_default_signer();
    let provider = context.get_default_provider();

    let tx_receipt = signer.send(script_pubkey.clone(), 1500)?;
    tx_receipt.wait()?;

    let multisig_utxos = provider.fetch_scripthash_utxos(&script_pubkey)?;

    assert!(
        multisig_utxos
            .iter()
            .any(|utxo| utxo.amount() == 1500 && utxo.txout.script_pubkey == script_pubkey)
    );

    Ok(())
}

#[simplex::test]
fn spend_multisig_with_two_of_three_votes(context: simplex::TestContext) -> anyhow::Result<()> {
    let scenario = SpendScenario {
        multisig_amounts: &[5_000],
        proposed_amounts: &[4_000],
        extra_amounts: &[],
        fee_amount: 3_000,
    };

    let tx = scenario.execute(&context)?;
    scenario.assert_transaction_shape(&tx);

    Ok(())
}

#[simplex::test]
fn spend_two_multisig_inputs_to_three_outputs(context: simplex::TestContext) -> anyhow::Result<()> {
    let scenario = SpendScenario {
        multisig_amounts: &[6_000, 7_000],
        proposed_amounts: &[3_000, 2_500, 2_000],
        extra_amounts: &[1_000],
        fee_amount: 6_500,
    };

    let tx = scenario.execute(&context)?;
    scenario.assert_transaction_shape(&tx);

    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct SpendScenario<'a> {
    multisig_amounts: &'a [u64],
    proposed_amounts: &'a [u64],
    extra_amounts: &'a [u64],
    fee_amount: u64,
}

impl SpendScenario<'_> {
    fn execute(self, context: &simplex::TestContext) -> anyhow::Result<Transaction> {
        let setup = Setup::new(2)?;
        let signer = context.get_default_signer();
        let provider = context.get_default_provider();
        let policy_asset = context.get_network().policy_asset();
        let recipient_script = signer.get_address().script_pubkey();
        let multisig_script = setup.multisig_builder.script_pubkey()?;

        let multisig_utxos = self
            .multisig_amounts
            .iter()
            .map(|amount| fund_script(context, &multisig_script, *amount))
            .collect::<anyhow::Result<Vec<_>>>()?;

        let outputs = self
            .proposed_amounts
            .iter()
            .chain(self.extra_amounts)
            .map(|amount| {
                Output::new_explicit(recipient_script.clone(), *amount, policy_asset, None)
            })
            .chain(std::iter::once(Output::new_explicit(
                Script::new(),
                self.fee_amount,
                policy_asset,
                None,
            )));
        let proposed_pst =
            create_proposed_multisig_spend(&multisig_script, &multisig_utxos, outputs);
        let total_proposed_outputs = u16::try_from(self.proposed_amounts.len())?;
        let first_vote = fund_vote(context, &setup, &proposed_pst, total_proposed_outputs, 0)?;
        let second_vote = fund_vote(context, &setup, &proposed_pst, total_proposed_outputs, 1)?;
        let final_pst = finalize_multisig_spend(
            &setup.multisig_builder,
            proposed_pst,
            multisig_utxos,
            &[Some(first_vote), Some(second_vote), None],
            total_proposed_outputs,
            context.get_network().genesis_block_hash(),
        )?;

        let tx = final_pst.extract_tx()?;
        let receipt = provider.broadcast_transaction(&tx)?;
        receipt.wait()?;

        Ok(provider.fetch_transaction(&receipt.txid())?)
    }

    fn assert_transaction_shape(self, tx: &Transaction) {
        let expected_output_count = self.proposed_amounts.len() + self.extra_amounts.len() + 1;

        assert_eq!(tx.input.len(), self.multisig_amounts.len() + 2);
        assert_eq!(tx.output.len(), expected_output_count);

        for (output, expected_amount) in tx.output.iter().zip(
            self.proposed_amounts
                .iter()
                .chain(self.extra_amounts)
                .copied()
                .chain(std::iter::once(self.fee_amount)),
        ) {
            assert_eq!(output.value.explicit(), Some(expected_amount));
        }
    }
}

fn fund_vote(
    context: &simplex::TestContext,
    setup: &Setup,
    proposed_pst: &simplex::simplicityhl::elements::pset::PartiallySignedTransaction,
    total_proposed_outputs: u16,
    participant_id: u32,
) -> anyhow::Result<VoteInput> {
    let vote = setup.vote_by(proposed_pst, total_proposed_outputs, participant_id)?;
    let vote_script = vote.script_pubkey()?;
    let utxo = fund_script(context, &vote_script, 1_000)?;

    Ok(VoteInput { vote, utxo })
}
