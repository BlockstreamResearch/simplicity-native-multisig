#![allow(clippy::wildcard_imports)]

use super::super::*;
use super::fixtures::*;

#[test]
fn participant_announcements_reconstruct_session_descriptor() -> anyhow::Result<()> {
    let mnemonics = distinct_mnemonics();
    let keys = participant_keys(mnemonics)?;
    let participant_descriptors = [
        "elwpkh([00000000/84h/1h/0h]tpubDUMMY/0/*)".to_owned(),
        "elwpkh([00000000/84h/1h/1h]tpubDUMMY/0/*)".to_owned(),
        "elwpkh([00000000/84h/1h/2h]tpubDUMMY/0/*)".to_owned(),
    ];

    let multisig_descriptor_json = create_multisig_descriptor(2, &serde_json::to_string(&keys)?)?;
    let multisig_descriptor: MultisigDescriptor = serde_json::from_str(&multisig_descriptor_json)?;
    let asset = AssetId::from_str(LIQUID_TESTNET_POLICY_ASSET)?;
    let mut announcements = Vec::new();

    for (index, participant_descriptor) in participant_descriptors.iter().enumerate() {
        let mut pset = PartiallySignedTransaction::new_v2();
        pset.add_output(Output::new_explicit(
            script_from_hex(&multisig_descriptor.multisig_script_pubkey)?,
            1_000,
            asset,
            None,
        ));
        let appended_json = append_participant_announcement_outputs(
            &pset.to_string(),
            &multisig_descriptor_json,
            participant_descriptor,
            mnemonics[index],
        )?;
        let appended: ParticipantAnnouncementAppendResultForTest =
            serde_json::from_str(&appended_json)?;
        let appended_pset = pset_from_base64(&appended.pset_base64)?;
        let tx = Transaction {
            version: 2,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: appended_pset
                .outputs()
                .iter()
                .map(Output::to_txout)
                .collect(),
        };
        let tx_hex = hex::encode(simplicityhl::elements::encode::serialize(&tx));
        let decoded_json =
            decode_participant_announcement_transaction(&multisig_descriptor_json, &tx_hex)?;
        let decoded: ParticipantAnnouncementForTest = serde_json::from_str(&decoded_json)?;

        assert_eq!(decoded.participant_index, index);
        assert_eq!(decoded.x_only_public_key, keys[index]);
        assert_eq!(decoded.participant_descriptor, *participant_descriptor);
        assert_eq!(appended.participant_index, index);
        announcements.push(decoded);
    }

    let session_json = create_session_from_participant_announcements(
        &multisig_descriptor_json,
        &serde_json::to_string(&announcements)?,
    )?;
    let session: MultisigSession = serde_json::from_str(&session_json)?;

    assert_eq!(session.threshold, 2);
    assert_eq!(
        session.multisig_script_pubkey,
        multisig_descriptor.multisig_script_pubkey
    );
    assert_eq!(session.participants.len(), PARTICIPANT_COUNT);
    for (index, participant) in session.participants.iter().enumerate() {
        assert_eq!(participant.x_only_public_key, keys[index]);
        assert_eq!(participant.vote_descriptor, participant_descriptors[index]);
    }

    Ok(())
}

#[test]
fn participant_announcement_rejects_blinding_material() -> anyhow::Result<()> {
    let keys = participant_keys(repeated_mnemonics())?;
    let multisig_descriptor_json = create_multisig_descriptor(2, &serde_json::to_string(&keys)?)?;
    let multisig_descriptor: MultisigDescriptor = serde_json::from_str(&multisig_descriptor_json)?;
    let mut pset = PartiallySignedTransaction::new_v2();
    pset.add_output(Output::new_explicit(
        script_from_hex(&multisig_descriptor.multisig_script_pubkey)?,
        1_000,
        AssetId::from_str(LIQUID_TESTNET_POLICY_ASSET)?,
        None,
    ));

    let error = append_participant_announcement_outputs(
        &pset.to_string(),
        &multisig_descriptor_json,
        &blinded_dummy_descriptors()[0],
        MNEMONIC,
    )
    .unwrap_err();

    assert_eq!(
        error.to_string(),
        "participant announcement descriptor must not include blinding material"
    );

    Ok(())
}

#[test]
fn participant_announcements_must_be_complete() -> anyhow::Result<()> {
    let keys = participant_keys(repeated_mnemonics())?;
    let multisig_descriptor_json = create_multisig_descriptor(2, &serde_json::to_string(&keys)?)?;

    let error = create_session_from_participant_announcements(
        &multisig_descriptor_json,
        &serde_json::to_string(&Vec::<ParticipantAnnouncementForTest>::new())?,
    )
    .unwrap_err();

    assert_eq!(error.to_string(), "missing participant 0 announcement");

    Ok(())
}
