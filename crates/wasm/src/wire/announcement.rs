#![allow(clippy::wildcard_imports)]

use serde::{Deserialize, Serialize};

use super::*;

const ANNOUNCEMENT_MAGIC: &[u8; 8] = b"SIMPANNC";
const ANNOUNCEMENT_VERSION_V1: u8 = 1;
const ANNOUNCEMENT_RECORD_METADATA: u8 = 0;
const ANNOUNCEMENT_RECORD_CHUNK: u8 = 1;
const ANNOUNCEMENT_HEADER_LEN: usize = ANNOUNCEMENT_MAGIC.len() + 2;
const ANNOUNCEMENT_METADATA_TOTAL_CHUNKS_OFFSET: usize = ANNOUNCEMENT_HEADER_LEN;
const ANNOUNCEMENT_METADATA_TOTAL_LEN_OFFSET: usize = ANNOUNCEMENT_METADATA_TOTAL_CHUNKS_OFFSET + 2;
const ANNOUNCEMENT_METADATA_CHECKSUM_OFFSET: usize = ANNOUNCEMENT_METADATA_TOTAL_LEN_OFFSET + 4;
const ANNOUNCEMENT_METADATA_LEN: usize = ANNOUNCEMENT_METADATA_CHECKSUM_OFFSET + 32;
const ANNOUNCEMENT_CHUNK_INDEX_OFFSET: usize = ANNOUNCEMENT_HEADER_LEN;
const ANNOUNCEMENT_CHUNK_DATA_OFFSET: usize = ANNOUNCEMENT_CHUNK_INDEX_OFFSET + 2;
const ANNOUNCEMENT_MAX_OP_RETURN_PAYLOAD_BYTES: usize = 75;
const ANNOUNCEMENT_MAX_CHUNK_DATA_BYTES: usize =
    ANNOUNCEMENT_MAX_OP_RETURN_PAYLOAD_BYTES - ANNOUNCEMENT_CHUNK_DATA_OFFSET;
const PARTICIPANT_ANNOUNCEMENT_PREFIX_LEN: usize = 1 + 32 + 64;

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnnouncementMetadata {
    total_chunks: u16,
    total_len: u32,
    checksum: sha256::Hash,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnnouncementChunk {
    index: u16,
    data: Vec<u8>,
}

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

struct AnnouncementPayload(Vec<u8>);

impl TryFrom<&Transaction> for AnnouncementPayload {
    type Error = anyhow::Error;

    fn try_from(tx: &Transaction) -> Result<Self, Self::Error> {
        let mut metadata = None;
        let mut chunks = Vec::new();
        for output in &tx.output {
            let Some((payload, has_extra_pushes)) = op_return_payload(&output.script_pubkey) else {
                continue;
            };
            if payload.len() < ANNOUNCEMENT_HEADER_LEN
                || &payload[..ANNOUNCEMENT_MAGIC.len()] != ANNOUNCEMENT_MAGIC
            {
                continue;
            }
            if has_extra_pushes {
                anyhow::bail!("participant announcement OP_RETURN output contains extra pushes");
            }
            if payload[ANNOUNCEMENT_MAGIC.len()] != ANNOUNCEMENT_VERSION_V1 {
                anyhow::bail!("unsupported participant announcement version");
            }

            match payload[ANNOUNCEMENT_MAGIC.len() + 1] {
                ANNOUNCEMENT_RECORD_METADATA => {
                    if payload.len() != ANNOUNCEMENT_METADATA_LEN {
                        anyhow::bail!("invalid participant announcement metadata length");
                    }
                    let next_metadata = AnnouncementMetadata {
                        total_chunks: u16::from_be_bytes(
                            payload[ANNOUNCEMENT_METADATA_TOTAL_CHUNKS_OFFSET
                                ..ANNOUNCEMENT_METADATA_TOTAL_CHUNKS_OFFSET + 2]
                                .try_into()?,
                        ),
                        total_len: u32::from_be_bytes(
                            payload[ANNOUNCEMENT_METADATA_TOTAL_LEN_OFFSET
                                ..ANNOUNCEMENT_METADATA_TOTAL_LEN_OFFSET + 4]
                                .try_into()?,
                        ),
                        checksum: sha256::Hash::from_byte_array(
                            payload[ANNOUNCEMENT_METADATA_CHECKSUM_OFFSET
                                ..ANNOUNCEMENT_METADATA_CHECKSUM_OFFSET + 32]
                                .try_into()?,
                        ),
                    };
                    if metadata.replace(next_metadata).is_some() {
                        anyhow::bail!("duplicate participant announcement metadata record");
                    }
                }
                ANNOUNCEMENT_RECORD_CHUNK => {
                    if payload.len() < ANNOUNCEMENT_CHUNK_DATA_OFFSET {
                        anyhow::bail!("invalid participant announcement chunk length");
                    }
                    chunks.push(AnnouncementChunk {
                        index: u16::from_be_bytes(
                            payload[ANNOUNCEMENT_CHUNK_INDEX_OFFSET
                                ..ANNOUNCEMENT_CHUNK_INDEX_OFFSET + 2]
                                .try_into()?,
                        ),
                        data: payload[ANNOUNCEMENT_CHUNK_DATA_OFFSET..].to_vec(),
                    });
                }
                _ => anyhow::bail!("unsupported participant announcement record type"),
            }
        }

        let metadata =
            metadata.ok_or_else(|| anyhow::anyhow!("missing participant announcement metadata"))?;
        if metadata.total_chunks == 0 {
            anyhow::bail!("participant announcement chunk count can not be zero");
        }

        let mut ordered = vec![None; usize::from(metadata.total_chunks)];
        for chunk in chunks {
            let index = usize::from(chunk.index);
            if index >= ordered.len() {
                anyhow::bail!("participant announcement chunk index is out of bounds");
            }
            if ordered[index].replace(chunk.data).is_some() {
                anyhow::bail!("duplicate participant announcement chunk");
            }
        }

        let mut data = Vec::with_capacity(usize::try_from(metadata.total_len)?);
        for (index, chunk) in ordered.into_iter().enumerate() {
            let chunk = chunk
                .ok_or_else(|| anyhow::anyhow!("missing participant announcement chunk {index}"))?;
            data.extend_from_slice(&chunk);
        }
        if data.len() != usize::try_from(metadata.total_len)? {
            anyhow::bail!("participant announcement length mismatch");
        }
        if sha256::Hash::hash(&data) != metadata.checksum {
            anyhow::bail!("participant announcement checksum mismatch");
        }

        Ok(Self(data))
    }
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
    let mut data = Vec::with_capacity(1 + 32 + 64 + participant_descriptor.len());
    data.push(u8::try_from(participant_index)?);
    data.extend_from_slice(&x_only_public_key_bytes);
    data.extend_from_slice(&signature.serialize());
    data.extend_from_slice(participant_descriptor.as_bytes());

    let total_chunks = data.len().div_ceil(ANNOUNCEMENT_MAX_CHUNK_DATA_BYTES);
    let total_chunks = u16::try_from(total_chunks)?;
    if total_chunks == 0 {
        anyhow::bail!("participant announcement payload can not be empty");
    }

    let checksum = sha256::Hash::hash(&data);
    let mut metadata = Vec::with_capacity(ANNOUNCEMENT_METADATA_LEN);
    metadata.extend_from_slice(ANNOUNCEMENT_MAGIC);
    metadata.push(ANNOUNCEMENT_VERSION_V1);
    metadata.push(ANNOUNCEMENT_RECORD_METADATA);
    metadata.extend_from_slice(&total_chunks.to_be_bytes());
    metadata.extend_from_slice(&u32::try_from(data.len())?.to_be_bytes());
    metadata.extend_from_slice(&checksum.to_byte_array());
    announcement_pst.add_output(announcement_output(&metadata, carrier_asset));

    for (index, chunk) in data.chunks(ANNOUNCEMENT_MAX_CHUNK_DATA_BYTES).enumerate() {
        let mut payload = Vec::with_capacity(ANNOUNCEMENT_CHUNK_DATA_OFFSET + chunk.len());
        payload.extend_from_slice(ANNOUNCEMENT_MAGIC);
        payload.push(ANNOUNCEMENT_VERSION_V1);
        payload.push(ANNOUNCEMENT_RECORD_CHUNK);
        payload.extend_from_slice(&u16::try_from(index)?.to_be_bytes());
        payload.extend_from_slice(chunk);
        announcement_pst.add_output(announcement_output(&payload, carrier_asset));
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

    let AnnouncementPayload(data) = AnnouncementPayload::try_from(&tx)?;

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

fn announcement_output(payload: &[u8], carrier_asset: AssetId) -> Output {
    debug_assert!(payload.len() <= ANNOUNCEMENT_MAX_OP_RETURN_PAYLOAD_BYTES);
    Output::new_explicit(Script::new_op_return(payload), 0, carrier_asset, None)
}

fn validate_public_participant_descriptor(participant_descriptor: &str) -> anyhow::Result<()> {
    let normalized = participant_descriptor.trim().to_ascii_lowercase();
    if normalized.starts_with("ct(") || normalized.contains("slip77(") {
        anyhow::bail!("participant announcement descriptor must not include blinding material");
    }

    Ok(())
}
