#![allow(clippy::wildcard_imports)]

use serde::{Deserialize, Serialize};

use contracts::common::chunked_records::RecordFraming;

use super::*;

const FRAMING: RecordFraming = RecordFraming {
    magic: b"SIMPANNC",
    version: 1,
    metadata_kind: 0,
    chunk_kind: 1,
    label: "participant announcement",
};
const PARTICIPANT_ANNOUNCEMENT_PREFIX_LEN: usize = 1 + 32 + 64;

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ParticipantAnnouncementAppendResult<'a> {
    pset_base64: &'a str,
    participant_index: usize,
    x_only_public_key: &'a str,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ParticipantAnnouncement {
    participant_index: usize,
    x_only_public_key: String,
    participant_descriptor: String,
    signature_hex: String,
}

/// Append authenticated participant descriptor announcement `OP_RETURN` outputs.
///
/// The caller provides a participant-funded PSET that already pays a dust amount
/// to the multisig address. This function signs the announced descriptor with
/// the matching covenant participant key and appends chunked `OP_RETURN` outputs.
pub fn append_participant_announcement_outputs(
    announcement_pset_base64: &str,
    multisig_descriptor_json: &str,
    participant_descriptor: &str,
    mnemonic: &str,
) -> anyhow::Result<String> {
    let descriptor: MultisigDescriptor = serde_json::from_str(multisig_descriptor_json)?;
    let builder = descriptor_builder(&descriptor)?;
    let mut announcement_pst = pset_from_base64(announcement_pset_base64)?;
    let (participant_index, keypair, _) = matching_participant_keypair(
        &descriptor.participants,
        mnemonic,
        "mnemonic does not match any participant key in this multisig descriptor",
        |participant| participant.index,
        |participant| participant.x_only_public_key.as_str(),
    )?;
    let x_only_public_key = descriptor.participants[participant_index]
        .x_only_public_key
        .clone();
    let carrier_asset = announcement_pst
        .outputs()
        .iter()
        .find_map(|output| output.asset)
        .ok_or_else(|| anyhow::anyhow!("announcement PSET has no explicit output asset"))?;

    let x_only_public_key_bytes = hex::decode(&x_only_public_key)?;
    if x_only_public_key_bytes.len() != 32 {
        anyhow::bail!("participant public key must be 32 bytes");
    }

    let participant_descriptor = participant_descriptor.trim();
    if participant_descriptor.is_empty() {
        anyhow::bail!("participant descriptor can not be empty");
    }
    validate_public_participant_descriptor(participant_descriptor)?;

    let message = participant_announcement_message(
        &descriptor,
        &builder,
        participant_index,
        &x_only_public_key_bytes,
        participant_descriptor,
    )?;
    let signature = SECP256K1.sign_schnorr(&message, &keypair);
    let mut data =
        Vec::with_capacity(PARTICIPANT_ANNOUNCEMENT_PREFIX_LEN + participant_descriptor.len());
    data.push(u8::try_from(participant_index)?);
    data.extend_from_slice(&x_only_public_key_bytes);
    data.extend_from_slice(&signature.serialize());
    data.extend_from_slice(participant_descriptor.as_bytes());

    for record in FRAMING.encode_payload(&data)? {
        announcement_pst.add_output(RecordFraming::record_output(&record, carrier_asset));
    }

    to_json(&ParticipantAnnouncementAppendResult {
        pset_base64: &announcement_pst.to_string(),
        participant_index,
        x_only_public_key: &x_only_public_key,
    })
}

/// Decode and verify one participant descriptor announcement from a transaction.
pub fn decode_participant_announcement_transaction(
    multisig_descriptor_json: &str,
    tx_hex: &str,
) -> anyhow::Result<String> {
    let descriptor: MultisigDescriptor = serde_json::from_str(multisig_descriptor_json)?;
    let builder = descriptor_builder(&descriptor)?;
    let tx: Transaction =
        simplicityhl::elements::encode::deserialize(&hex::decode(tx_hex.trim())?)?;
    let multisig_script = builder.script_pubkey()?;
    let pays_multisig = tx.output.iter().any(|output| {
        output.script_pubkey == multisig_script && output.value.explicit().unwrap_or(0) > 0
    });
    if !pays_multisig {
        anyhow::bail!("participant announcement transaction does not fund the multisig");
    }

    let data = FRAMING.decode_transaction(&tx, |_, _| {
        anyhow::bail!("unsupported participant announcement record type")
    })?;

    if data.len() <= PARTICIPANT_ANNOUNCEMENT_PREFIX_LEN {
        anyhow::bail!("participant announcement payload is truncated");
    }

    let participant_index = usize::from(data[0]);
    if participant_index >= PARTICIPANT_COUNT {
        anyhow::bail!("participant announcement index is out of bounds");
    }

    let x_only_public_key = hex::encode(&data[1..33]);
    let expected_key = &descriptor.participants[participant_index].x_only_public_key;
    if &x_only_public_key != expected_key {
        anyhow::bail!("participant announcement key does not match multisig descriptor");
    }

    let signature = Signature::from_slice(&data[33..97]).map_err(anyhow::Error::msg)?;
    let participant_descriptor = std::str::from_utf8(&data[97..])?.to_owned();
    validate_public_participant_descriptor(&participant_descriptor)?;
    let message = participant_announcement_message(
        &descriptor,
        &builder,
        participant_index,
        &data[1..33],
        &participant_descriptor,
    )?;
    SECP256K1
        .verify_schnorr(
            &signature,
            &message,
            &x_only_pubkey_from_hex(&x_only_public_key)?,
        )
        .map_err(|_| anyhow::anyhow!("participant announcement signature is invalid"))?;

    let announcement = ParticipantAnnouncement {
        participant_index,
        x_only_public_key,
        participant_descriptor,
        signature_hex: hex::encode(signature.serialize()),
    };

    to_json(&announcement)
}

/// Create a full session after all participant announcements are available.
pub fn create_session_from_participant_announcements(
    multisig_descriptor_json: &str,
    announcements_json: &str,
) -> anyhow::Result<String> {
    let descriptor: MultisigDescriptor = serde_json::from_str(multisig_descriptor_json)?;
    let builder = descriptor_builder(&descriptor)?;
    let announcements: Vec<ParticipantAnnouncement> = serde_json::from_str(announcements_json)?;
    let mut descriptors = vec![None; PARTICIPANT_COUNT];

    for announcement in announcements {
        if announcement.participant_index >= PARTICIPANT_COUNT {
            anyhow::bail!("participant announcement index is out of bounds");
        }

        let expected_key =
            &descriptor.participants[announcement.participant_index].x_only_public_key;
        if &announcement.x_only_public_key != expected_key {
            anyhow::bail!("participant announcement key does not match multisig descriptor");
        }
        validate_public_participant_descriptor(&announcement.participant_descriptor)?;

        let slot = &mut descriptors[announcement.participant_index];
        if let Some(current) = slot {
            if current != &announcement.participant_descriptor {
                anyhow::bail!("conflicting descriptor announcements for participant");
            }
        } else {
            *slot = Some(announcement.participant_descriptor);
        }
    }

    let participant_descriptors = descriptors
        .into_iter()
        .enumerate()
        .map(|(index, descriptor)| {
            descriptor.ok_or_else(|| anyhow::anyhow!("missing participant {index} announcement"))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;

    session_from_parts(
        descriptor.threshold,
        descriptor
            .participants
            .into_iter()
            .map(|participant| participant.x_only_public_key)
            .collect(),
        participant_descriptors,
        &builder,
    )
}

fn participant_announcement_message(
    descriptor: &MultisigDescriptor,
    builder: &MultisigBuilder,
    participant_index: usize,
    x_only_public_key: &[u8],
    participant_descriptor: &str,
) -> anyhow::Result<Message> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"SIMPANNOUNCE-V1");
    bytes.extend_from_slice(builder.script_pubkey()?.as_bytes());
    bytes.push(u8::try_from(participant_index)?);
    bytes.extend_from_slice(x_only_public_key);
    bytes.extend_from_slice(descriptor.threshold.to_be_bytes().as_slice());
    bytes.extend_from_slice(participant_descriptor.as_bytes());
    let hash = sha256::Hash::hash(&bytes);

    Ok(Message::from_digest(hash.to_byte_array()))
}

fn validate_public_participant_descriptor(participant_descriptor: &str) -> anyhow::Result<()> {
    let normalized = participant_descriptor.trim().to_ascii_lowercase();
    if normalized.starts_with("ct(") || normalized.contains("slip77(") {
        anyhow::bail!("participant announcement descriptor must not include blinding material");
    }

    Ok(())
}
