#![allow(clippy::wildcard_imports)]

use self::types::{
    ExecutorFundedSpendPlan, FinalizedSpendResult, PreparedSpendPlan, ProposalResult, PsetResult,
    SpendPlan, WireOutput, WireOutputKind, WireVoteInput,
};
use super::*;

mod types;

/// Build a proposal PSET from selected multisig UTXOs and simple outputs.
///
/// `utxos_json` is an array of [`WireUtxo`]. `outputs_json` is an array of
/// [`WireOutput`]. Transfer and burn outputs are signed by the vote; fee outputs
/// are appended but excluded from `total_proposed_outputs`.
pub fn create_proposed_spend(
    session_json: &str,
    utxos_json: &str,
    outputs_json: &str,
) -> anyhow::Result<String> {
    let session: MultisigSession = serde_json::from_str(session_json)?;
    let builder = session_builder(&session)?;
    let multisig_script = builder.script_pubkey()?;
    let utxos = wire_utxos_into_utxos(serde_json::from_str(utxos_json)?)?;
    let wire_outputs: Vec<WireOutput> = serde_json::from_str(outputs_json)?;

    let mut total_proposed_outputs = 0_u16;
    let mut signed_outputs = Vec::with_capacity(wire_outputs.len());
    let mut fee_outputs = Vec::new();
    for output in wire_outputs {
        let WireOutput {
            kind,
            script_pubkey,
            address,
            asset,
            value,
        } = output;
        let is_fee = matches!(kind, WireOutputKind::Fee);
        let asset = AssetId::from_str(&asset)?;
        let script = match kind {
            WireOutputKind::Transfer => {
                if value == 0 {
                    anyhow::bail!("transfer output amount must be greater than zero");
                }
                if let Some(script_pubkey) = script_pubkey {
                    script_from_hex(&script_pubkey)?
                } else if let Some(address) = address {
                    Address::from_str(&address)?.script_pubkey()
                } else {
                    anyhow::bail!("transfer output requires address or scriptPubkey");
                }
            }
            WireOutputKind::Burn => {
                if value == 0 {
                    anyhow::bail!("burn output amount must be greater than zero");
                }
                Script::new_op_return(b"burn")
            }
            WireOutputKind::Fee => Script::new(),
        };
        let output = Output::new_explicit(script, value, asset, None);
        if is_fee {
            fee_outputs.push(output);
        } else {
            total_proposed_outputs = total_proposed_outputs
                .checked_add(1)
                .ok_or_else(|| anyhow::anyhow!("too many proposed outputs"))?;
            signed_outputs.push(output);
        }
    }
    signed_outputs.extend(fee_outputs);

    let mut proposed_pst = create_proposed_multisig_spend(&multisig_script, &utxos, signed_outputs);
    attach_missing_witness_utxos(&mut proposed_pst, &utxos);
    let proposed_tx = proposed_pst.extract_tx()?;
    verify_proposal_balance(&builder, &proposed_pst, total_proposed_outputs)?;
    let vote_plan = create_vote(&builder, &proposed_pst, total_proposed_outputs)?;

    to_json(&ProposalResult {
        pset_base64: &proposed_pst.to_string(),
        tx_hex: &hex::encode(simplicityhl::elements::encode::serialize(&proposed_tx)),
        total_proposed_outputs,
        message_hash: &vote_plan.message_hash().to_string(),
    })
}

/// Finalize a multisig spend from one high-level request payload.
pub fn finalize_spend_plan(plan_json: &str) -> anyhow::Result<String> {
    let plan: SpendPlan = serde_json::from_str(plan_json)?;
    let session = plan.session;
    let builder = session_builder(&session)?;
    let mut proposed_pst = pset_from_base64(&plan.proposed_pset_base64)?;
    let proposed_input_utxos = wire_utxos_into_utxos(plan.multisig_utxos)?;
    let vote_inputs = wire_vote_inputs_into_slots(
        &builder,
        &proposed_pst,
        plan.total_proposed_outputs,
        plan.vote_inputs,
    )?;

    append_vote_input_fee_outputs(&mut proposed_pst, &vote_inputs)?;
    merge_fee_outputs(&mut proposed_pst)?;

    finalized_spend_json(&finalize_multisig_spend(
        &builder,
        proposed_pst,
        proposed_input_utxos,
        &vote_inputs,
        plan.total_proposed_outputs,
        liquid_testnet_genesis_hash(),
    )?)
}

/// Prepare a final spend with executor fee funding from one high-level request payload.
pub fn prepare_executor_funded_spend(plan_json: &str) -> anyhow::Result<String> {
    let plan: ExecutorFundedSpendPlan = serde_json::from_str(plan_json)?;
    let session = plan.spend.session;
    let builder = session_builder(&session)?;
    let mut proposed_pst = pset_from_base64(&plan.spend.proposed_pset_base64)?;
    let mut proposed_input_utxos = wire_utxos_into_utxos(plan.spend.multisig_utxos)?;
    let vote_inputs = wire_vote_inputs_into_slots(
        &builder,
        &proposed_pst,
        plan.spend.total_proposed_outputs,
        plan.spend.vote_inputs,
    )?;
    let executor_input_secrets = plan
        .executor_input_secrets
        .into_iter()
        .map(|secrets| {
            Ok(TxOutSecrets::new(
                AssetId::from_str(&secrets.asset)?,
                AssetBlindingFactor::from_str(&secrets.asset_blinding_factor)?,
                secrets.value,
                ValueBlindingFactor::from_str(&secrets.value_blinding_factor)?,
            ))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;

    append_vote_input_fee_outputs(&mut proposed_pst, &vote_inputs)?;
    let executor_pst = pset_from_base64(&plan.executor_pset_base64)?;
    if executor_pst.inputs().len() != executor_input_secrets.len() {
        anyhow::bail!("executor input secret count does not match executor PSET inputs");
    }

    let input_offset = u32::try_from(proposed_pst.inputs().len())?;
    for (input, secrets) in executor_pst.inputs().iter().zip(&executor_input_secrets) {
        let mut utxo = pset_input_utxo(input)?;
        utxo.secrets = Some(*secrets);
        proposed_input_utxos.push(utxo);
        proposed_pst.add_input(input.clone());
    }

    for output in executor_pst.outputs() {
        let mut output = output.clone();
        if let Some(blinder_index) = output.blinder_index {
            output.blinder_index = Some(
                blinder_index
                    .checked_add(input_offset)
                    .ok_or_else(|| anyhow::anyhow!("executor output blinder index overflow"))?,
            );
            output.amount_comm = None;
            output.asset_comm = None;
            output.value_rangeproof = None;
            output.asset_surjection_proof = None;
            output.ecdh_pubkey = None;
            output.blind_value_proof = None;
            output.blind_asset_proof = None;
        }
        proposed_pst.add_output(output);
    }
    merge_fee_outputs(&mut proposed_pst)?;

    let (mut prepared_pst, input_utxos, _) =
        prepare_multisig_spend_inputs(&builder, proposed_pst, proposed_input_utxos, &vote_inputs)?;
    let input_secrets = input_utxos
        .iter()
        .enumerate()
        .map(|(index, utxo)| {
            if let Some(secrets) = utxo.secrets {
                return Ok((index, secrets));
            }

            let asset = utxo.txout.asset.explicit().ok_or_else(|| {
                anyhow::anyhow!("input asset is confidential and no blinding secret was provided")
            })?;
            let value = utxo.txout.value.explicit().ok_or_else(|| {
                anyhow::anyhow!("input value is confidential and no blinding secret was provided")
            })?;

            Ok((
                index,
                TxOutSecrets::new(
                    asset,
                    AssetBlindingFactor::zero(),
                    value,
                    ValueBlindingFactor::zero(),
                ),
            ))
        })
        .collect::<anyhow::Result<HashMap<_, _>>>()?;
    prepared_pst.global.scalars.clear();
    prepared_pst
        .blind_last(&mut thread_rng(), SECP256K1, &input_secrets)
        .map_err(anyhow::Error::msg)?;

    to_json(&PsetResult {
        pset_base64: &prepared_pst.to_string(),
    })
}

/// Add covenant witnesses to an already signed/blinded prepared spend request.
pub fn finalize_prepared_spend_plan(plan_json: &str) -> anyhow::Result<String> {
    let plan: PreparedSpendPlan = serde_json::from_str(plan_json)?;
    let session = plan.spend.session;
    let builder = session_builder(&session)?;
    let proposed_pst = pset_from_base64(&plan.spend.proposed_pset_base64)?;
    let prepared_pst = pset_from_base64(&plan.prepared_pset_base64)?;
    let vote_inputs = wire_vote_inputs_into_slots(
        &builder,
        &proposed_pst,
        plan.spend.total_proposed_outputs,
        plan.spend.vote_inputs,
    )?;
    let multisig_input_count = plan.spend.multisig_utxos.len();
    let mut input_utxos = wire_utxos_into_utxos(plan.spend.multisig_utxos)?;
    for vote_input in vote_inputs.iter().flatten() {
        input_utxos.push(vote_input.utxo.clone());
    }

    for input in prepared_pst.inputs().iter().skip(input_utxos.len()) {
        input_utxos.push(pset_input_utxo(input)?);
    }
    if prepared_pst.inputs().len() != input_utxos.len() {
        anyhow::bail!("prepared PSET input count does not match reconstructed UTXOs");
    }

    finalized_spend_json(&finalize_prepared_multisig_spend(
        &builder,
        prepared_pst,
        &input_utxos,
        &vote_inputs,
        multisig_input_count,
        plan.spend.total_proposed_outputs,
        liquid_testnet_genesis_hash(),
    )?)
}

fn liquid_testnet_genesis_hash() -> BlockHash {
    BlockHash::from_byte_array(LIQUID_TESTNET_GENESIS_BYTES)
}

pub(super) fn wire_utxos_into_utxos(utxos: Vec<WireUtxo>) -> anyhow::Result<Vec<Utxo>> {
    utxos.into_iter().map(wire_utxo_into_utxo).collect()
}

fn wire_utxo_into_utxo(utxo: WireUtxo) -> anyhow::Result<Utxo> {
    Ok(Utxo {
        outpoint: OutPoint::new(Txid::from_str(&utxo.txid)?, utxo.vout),
        txout: TxOut {
            asset: confidential::Asset::Explicit(AssetId::from_str(&utxo.asset)?),
            value: confidential::Value::Explicit(utxo.value),
            nonce: confidential::Nonce::Null,
            script_pubkey: script_from_hex(&utxo.script_pubkey)?,
            witness: TxOutWitness::default(),
        },
        secrets: None,
    })
}

fn wire_vote_inputs_into_slots(
    builder: &MultisigBuilder,
    proposed_pst: &PartiallySignedTransaction,
    total_proposed_outputs: u16,
    vote_inputs: Vec<WireVoteInput>,
) -> anyhow::Result<[Option<VoteInput>; PARTICIPANT_COUNT]> {
    let vote_plan = create_vote(builder, proposed_pst, total_proposed_outputs)?;
    let mut slots: [Option<VoteInput>; PARTICIPANT_COUNT] = [None, None, None];

    for vote_input in vote_inputs {
        if vote_input.participant_index >= PARTICIPANT_COUNT {
            anyhow::bail!("participant index is out of bounds");
        }
        let signature = signature_from_hex(&vote_input.signature_hex)?;
        slots[vote_input.participant_index] = Some(VoteInput {
            vote: vote_plan.signed_vote(signature),
            utxo: wire_utxo_into_utxo(vote_input.utxo)?,
        });
    }

    Ok(slots)
}

fn append_vote_input_fee_outputs(
    proposed_pst: &mut PartiallySignedTransaction,
    vote_inputs: &[Option<VoteInput>; PARTICIPANT_COUNT],
) -> anyhow::Result<()> {
    let mut fee_by_asset = Vec::<(AssetId, u64)>::new();

    for vote_input in vote_inputs.iter().flatten() {
        let (asset, amount) = if let Some(secrets) = vote_input.utxo.secrets {
            (secrets.asset, secrets.value)
        } else {
            (
                vote_input
                    .utxo
                    .txout
                    .asset
                    .explicit()
                    .ok_or_else(|| anyhow::anyhow!("vote input asset is confidential"))?,
                vote_input
                    .utxo
                    .txout
                    .value
                    .explicit()
                    .ok_or_else(|| anyhow::anyhow!("vote input value is confidential"))?,
            )
        };
        add_fee_total(
            &mut fee_by_asset,
            asset,
            amount,
            "vote input fee amount overflow",
        )?;
    }

    for (asset, amount) in fee_by_asset {
        proposed_pst.add_output(Output::new_explicit(Script::new(), amount, asset, None));
    }

    Ok(())
}

fn merge_fee_outputs(proposed_pst: &mut PartiallySignedTransaction) -> anyhow::Result<()> {
    let mut fee_totals = Vec::<(AssetId, u64)>::new();
    let mut fee_indexes = Vec::new();

    for (index, output) in proposed_pst.outputs().iter().enumerate() {
        if !output.script_pubkey.is_empty() {
            continue;
        }

        let asset = output
            .asset
            .ok_or_else(|| anyhow::anyhow!("fee output asset must be explicit"))?;
        let amount = output
            .amount
            .ok_or_else(|| anyhow::anyhow!("fee output amount must be explicit"))?;

        add_fee_total(&mut fee_totals, asset, amount, "fee output amount overflow")?;
        fee_indexes.push(index);
    }

    for index in fee_indexes.into_iter().rev() {
        proposed_pst.remove_output(index);
    }
    for (asset, amount) in fee_totals {
        proposed_pst.add_output(Output::new_explicit(Script::new(), amount, asset, None));
    }

    Ok(())
}

fn add_fee_total(
    fee_totals: &mut Vec<(AssetId, u64)>,
    asset: AssetId,
    amount: u64,
    overflow_message: &str,
) -> anyhow::Result<()> {
    if let Some((_, total)) = fee_totals
        .iter_mut()
        .find(|(current_asset, _)| *current_asset == asset)
    {
        *total = total
            .checked_add(amount)
            .ok_or_else(|| anyhow::anyhow!("{overflow_message}"))?;
    } else {
        fee_totals.push((asset, amount));
    }

    Ok(())
}

fn finalized_spend_json(final_pst: &PartiallySignedTransaction) -> anyhow::Result<String> {
    let final_tx = final_pst.extract_tx()?;

    to_json(&FinalizedSpendResult {
        pset_base64: &final_pst.to_string(),
        tx_hex: &hex::encode(simplicityhl::elements::encode::serialize(&final_tx)),
        txid: &final_tx.txid().to_string(),
    })
}

fn pset_input_utxo(input: &simplicityhl::elements::pset::Input) -> anyhow::Result<Utxo> {
    let outpoint = OutPoint::new(input.previous_txid, input.previous_output_index);
    let txout = match (&input.witness_utxo, &input.non_witness_utxo) {
        (Some(txout), _) => txout.clone(),
        (None, Some(tx)) => tx
            .output
            .get(usize::try_from(input.previous_output_index)?)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("executor input prevout is missing from transaction"))?,
        (None, None) => anyhow::bail!("executor input is missing witness_utxo"),
    };

    Ok(Utxo {
        outpoint,
        txout,
        secrets: None,
    })
}
