#![allow(clippy::wildcard_imports)]

use super::super::*;
use super::fixtures::*;
use simplicityhl::elements::bitcoin::secp256k1;
use simplicityhl::elements::pset::Input;

#[test]
fn finalization_accounts_for_vote_input_value_as_fee() -> anyhow::Result<()> {
    let fixture = proposal_fixture(4_300, 4_000, 300)?;
    let vote_inputs = vote_inputs_json(
        &fixture.session_json,
        &fixture.proposal,
        distinct_mnemonics(),
    )?;
    let finalized_json = finalize_spend_plan(
        &serde_json::json!({
            "session": fixture.session,
            "proposedPsetBase64": fixture.proposal.pset_base64,
            "multisigUtxos": serde_json::from_str::<serde_json::Value>(&fixture.multisig_utxos)?,
            "voteInputs": serde_json::from_str::<serde_json::Value>(&vote_inputs)?,
            "totalProposedOutputs": fixture.proposal.total_proposed_outputs
        })
        .to_string(),
    )?;
    let finalized: serde_json::Value = serde_json::from_str(&finalized_json)?;
    let tx_hex = finalized
        .get("txHex")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| anyhow::anyhow!("finalized txHex is missing"))?;
    let tx: Transaction = simplicityhl::elements::encode::deserialize(&hex::decode(tx_hex)?)?;

    assert_eq!(tx.input.len(), 3);
    assert_eq!(tx.output.len(), 2);
    assert_eq!(tx.output[0].value.explicit(), Some(4_000));
    assert_eq!(tx.output[1].value.explicit(), Some(2_300));
    assert!(!tx.output[0].script_pubkey.is_empty());
    assert!(tx.output[1].script_pubkey.is_empty());

    Ok(())
}

#[test]
fn prepared_executor_pset_is_blinded_after_final_shape_is_known() -> anyhow::Result<()> {
    let fixture = proposal_fixture(4_300, 4_000, 300)?;
    let vote_inputs_json = vote_inputs_json(
        &fixture.session_json,
        &fixture.proposal,
        distinct_mnemonics(),
    )?;
    let multisig_utxos = serde_json::from_str::<serde_json::Value>(&fixture.multisig_utxos)?;
    let vote_inputs = serde_json::from_str::<serde_json::Value>(&vote_inputs_json)?;
    let secp = secp256k1::Secp256k1::new();
    let blinding_secret = secp256k1::SecretKey::from_slice(&[7_u8; 32])?;
    let blinding_key = simplicityhl::elements::bitcoin::PublicKey::new(
        secp256k1::PublicKey::from_secret_key(&secp, &blinding_secret),
    );
    let asset = AssetId::from_str(LIQUID_TESTNET_POLICY_ASSET)?;
    let executor_txid =
        Txid::from_str("0404040404040404040404040404040404040404040404040404040404040404")?;
    let mut executor_pst = PartiallySignedTransaction::new_v2();
    let mut input = Input::from_prevout(OutPoint::new(executor_txid, 0));
    input.witness_utxo = Some(TxOut {
        asset: confidential::Asset::Explicit(asset),
        value: confidential::Value::Explicit(1_500),
        nonce: confidential::Nonce::Null,
        script_pubkey: Script::new_op_return(b"executor"),
        witness: TxOutWitness::default(),
    });
    executor_pst.add_input(input);

    let change_script = Script::new_op_return(b"change");
    let mut change = Output::new_explicit(change_script, 1_200, asset, Some(blinding_key));
    change.blinder_index = Some(0);
    executor_pst.add_output(change);
    executor_pst.add_output(Output::new_explicit(Script::new(), 300, asset, None));

    let prepared_json = prepare_executor_funded_spend(
        &serde_json::json!({
            "session": fixture.session,
            "proposedPsetBase64": fixture.proposal.pset_base64,
            "multisigUtxos": multisig_utxos,
            "voteInputs": vote_inputs,
            "executorPsetBase64": executor_pst.to_string(),
            "executorInputSecrets": [{
                "asset": LIQUID_TESTNET_POLICY_ASSET,
                "value": 1_500,
                "assetBlindingFactor": AssetBlindingFactor::zero().to_string(),
                "valueBlindingFactor": ValueBlindingFactor::zero().to_string()
            }],
            "totalProposedOutputs": fixture.proposal.total_proposed_outputs
        })
        .to_string(),
    )?;
    let prepared: serde_json::Value = serde_json::from_str(&prepared_json)?;
    let prepared_pset_base64 = prepared
        .get("psetBase64")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| anyhow::anyhow!("prepared psetBase64 is missing"))?;
    let prepared_pset = pset_from_base64(prepared_pset_base64)?;
    let prepared_tx = prepared_pset.extract_tx()?;

    assert_eq!((prepared_tx.input.len(), prepared_tx.output.len()), (4, 3));
    assert_eq!(prepared_tx.input[3].previous_output.txid, executor_txid);
    assert_eq!(prepared_tx.output[0].value.explicit(), Some(4_000));
    assert_eq!(prepared_tx.output[2].value.explicit(), Some(2_600));
    assert_eq!(prepared_pset.outputs()[1].blinder_index, Some(3));
    assert!(prepared_pset.outputs()[1].amount_comm.is_some());
    assert!(prepared_pset.outputs()[1].asset_comm.is_some());
    assert!(prepared_pset.outputs()[1].value_rangeproof.is_some());
    assert!(prepared_pset.outputs()[1].asset_surjection_proof.is_some());
    let blinded_output = &prepared_tx.output[1];
    assert!(matches!(
        blinded_output.value,
        confidential::Value::Confidential(_)
    ));
    assert!(matches!(
        blinded_output.asset,
        confidential::Asset::Confidential(_)
    ));

    let finalized_json = finalize_prepared_spend_plan(
        &serde_json::json!({
            "session": fixture.session,
            "proposedPsetBase64": fixture.proposal.pset_base64,
            "preparedPsetBase64": prepared_pset_base64,
            "multisigUtxos": multisig_utxos,
            "voteInputs": vote_inputs,
            "totalProposedOutputs": fixture.proposal.total_proposed_outputs
        })
        .to_string(),
    )?;
    let finalized: serde_json::Value = serde_json::from_str(&finalized_json)?;
    let finalized_tx_hex = finalized
        .get("txHex")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| anyhow::anyhow!("finalized txHex is missing"))?;
    let finalized_tx: Transaction =
        simplicityhl::elements::encode::deserialize(&hex::decode(finalized_tx_hex)?)?;

    assert_eq!(
        (finalized_tx.input.len(), finalized_tx.output.len()),
        (4, 3)
    );

    Ok(())
}
