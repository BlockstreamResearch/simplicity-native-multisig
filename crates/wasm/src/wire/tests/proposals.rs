#![allow(clippy::wildcard_imports)]

use super::super::*;
use super::fixtures::*;

#[test]
fn create_proposed_spend_rejects_zero_transfer_and_burn_amounts() -> anyhow::Result<()> {
    let (session_json, session) = session(repeated_mnemonics())?;
    let utxos_json = multisig_utxos_json(&session, 10_000);
    let zero_transfer = serde_json::json!([
        {
            "kind": "transfer",
            "address": session.multisig_address,
            "asset": LIQUID_TESTNET_POLICY_ASSET,
            "value": 0
        }
    ])
    .to_string();

    let zero_transfer_error =
        create_proposed_spend(&session_json, &utxos_json, &zero_transfer).unwrap_err();

    assert_eq!(
        zero_transfer_error.to_string(),
        "transfer output amount must be greater than zero"
    );

    let zero_burn = serde_json::json!([
        {
            "kind": "burn",
            "asset": LIQUID_TESTNET_POLICY_ASSET,
            "value": 0
        }
    ])
    .to_string();
    let zero_burn_error =
        create_proposed_spend(&session_json, &utxos_json, &zero_burn).unwrap_err();

    assert_eq!(
        zero_burn_error.to_string(),
        "burn output amount must be greater than zero"
    );

    Ok(())
}

#[test]
fn create_proposed_spend_rejects_negative_amount_json() -> anyhow::Result<()> {
    let (session_json, session) = session(repeated_mnemonics())?;
    let utxos_json = multisig_utxos_json(&session, 10_000);
    let negative_output = format!(
        r#"[{{"kind":"transfer","address":"{}","asset":"{}","value":-1}}]"#,
        session.multisig_address, LIQUID_TESTNET_POLICY_ASSET
    );

    let error = create_proposed_spend(&session_json, &utxos_json, &negative_output)
        .unwrap_err()
        .to_string();

    assert!(error.contains("invalid value"));
    assert!(error.contains("expected u64"));

    Ok(())
}

#[test]
fn auto_decodes_vote_transaction_with_vote_utxo() -> anyhow::Result<()> {
    let fixture = proposal_fixture(1_200, 1_000, 200)?;
    let proposed_pst = pset_from_base64(&fixture.proposal.pset_base64)?;
    let proposed_tx = proposed_pst.extract_tx()?;

    assert_eq!(fixture.proposal.total_proposed_outputs, 1);
    assert!(!proposed_tx.output[0].script_pubkey.is_empty());
    assert!(proposed_tx.output[1].script_pubkey.is_empty());

    let (keypair, _) = derive_keypair(MNEMONIC, 0)?;
    let builder = session_builder(&fixture.session)?;
    let vote = create_vote(
        &builder,
        &proposed_pst,
        fixture.proposal.total_proposed_outputs,
    )?
    .sign(&keypair);
    let vote_script = vote.script_pubkey()?;
    let mut outputs = vec![TxOut {
        asset: confidential::Asset::Explicit(AssetId::from_str(LIQUID_TESTNET_POLICY_ASSET)?),
        value: confidential::Value::Explicit(1_000),
        nonce: confidential::Nonce::Null,
        script_pubkey: vote_script,
        witness: TxOutWitness::default(),
    }];
    outputs.extend(
        onchain_encoder::encode(&proposed_pst, vote.signature())?
            .into_iter()
            .map(|output| output.to_txout()),
    );
    let vote_tx = Transaction {
        version: 2,
        lock_time: LockTime::ZERO,
        input: Vec::new(),
        output: outputs,
    };
    let vote_tx_hex = hex::encode(simplicityhl::elements::encode::serialize(&vote_tx));
    let decoded_json = decode_vote_transaction_auto(&fixture.session_json, &vote_tx_hex)?;
    let decoded: DecodedVoteResultForTest = serde_json::from_str(&decoded_json)?;

    assert_eq!(
        decoded.proposed_tx_hex,
        hex::encode(simplicityhl::elements::encode::serialize(&proposed_tx))
    );
    assert_eq!(decoded.participant_index, 0);
    assert_eq!(decoded.total_proposed_outputs, 1);
    assert_eq!(decoded.proposal_input_outpoints.len(), 1);
    assert_eq!(decoded.vote_utxo.txid, vote_tx.txid().to_string());
    assert_eq!(decoded.vote_utxo.vout, 0);

    Ok(())
}
