//! Chunked `OP_RETURN` record framing shared by the on-chain wire formats.
//!
//! A payload is split into chunks that each fit into one standard `OP_RETURN`
//! data push. A metadata record announces the chunk count, the total payload
//! length, and a SHA-256 checksum of the reassembled payload. Record kinds
//! outside the shared metadata/chunk pair (such as the vote signature record)
//! are dispatched back to the caller.

use simplicityhl::elements::hashes::{Hash, sha256};
use simplicityhl::elements::pset::Output;
use simplicityhl::elements::{AssetId, Script, Transaction};

use super::op_return_payload;

/// Largest payload expressible with a single direct push opcode.
pub const MAX_OP_RETURN_PAYLOAD_BYTES: usize = 75;
const MAGIC_LEN: usize = 8;
/// Magic, version, and record kind.
pub const RECORD_HEADER_LEN: usize = MAGIC_LEN + 2;
const CHUNK_DATA_OFFSET: usize = RECORD_HEADER_LEN + 2;
/// Payload bytes carried by one chunk record.
pub const MAX_CHUNK_DATA_BYTES: usize = MAX_OP_RETURN_PAYLOAD_BYTES - CHUNK_DATA_OFFSET;
const METADATA_TOTAL_LEN_OFFSET: usize = RECORD_HEADER_LEN + 2;
const METADATA_CHECKSUM_OFFSET: usize = METADATA_TOTAL_LEN_OFFSET + 4;
const METADATA_LEN: usize = METADATA_CHECKSUM_OFFSET + 32;

/// Framing constants for one chunked record format.
pub struct RecordFraming {
    /// 8-byte record magic.
    pub magic: &'static [u8; 8],
    /// Format version byte.
    pub version: u8,
    /// Record kind carrying the metadata record.
    pub metadata_kind: u8,
    /// Record kind carrying payload chunks.
    pub chunk_kind: u8,
    /// Payload name used in error messages.
    pub label: &'static str,
}

impl RecordFraming {
    /// Record header shared by every record of this format.
    #[must_use]
    pub fn record_prefix(&self, kind: u8) -> Vec<u8> {
        let mut payload = Vec::with_capacity(MAX_OP_RETURN_PAYLOAD_BYTES);
        payload.extend_from_slice(self.magic);
        payload.push(self.version);
        payload.push(kind);
        payload
    }

    /// Encode `data` as a metadata record followed by chunk records.
    pub fn encode_payload(&self, data: &[u8]) -> anyhow::Result<Vec<Vec<u8>>> {
        let label = self.label;
        if data.is_empty() {
            anyhow::bail!("{label} payload can not be empty");
        }
        let total_len = u32::try_from(data.len())
            .map_err(|_| anyhow::anyhow!("encoded {label} is too large"))?;
        let total_chunks = data.len().div_ceil(MAX_CHUNK_DATA_BYTES);
        let total_chunks = u16::try_from(total_chunks)
            .map_err(|_| anyhow::anyhow!("encoded {label} needs too many outputs"))?;

        let mut metadata = self.record_prefix(self.metadata_kind);
        metadata.extend_from_slice(&total_chunks.to_be_bytes());
        metadata.extend_from_slice(&total_len.to_be_bytes());
        metadata.extend_from_slice(sha256::Hash::hash(data).as_byte_array());

        let mut records = vec![metadata];
        records.extend(
            data.chunks(MAX_CHUNK_DATA_BYTES)
                .enumerate()
                .map(|(index, chunk)| {
                    let mut record = self.record_prefix(self.chunk_kind);
                    record.extend_from_slice(
                        &u16::try_from(index)
                            .expect("chunk count is already bounded")
                            .to_be_bytes(),
                    );
                    record.extend_from_slice(chunk);
                    record
                }),
        );

        Ok(records)
    }

    /// Reassemble and validate the payload carried by `transaction`.
    ///
    /// Records with a kind other than metadata or chunk are passed to `extra`
    /// together with the full record payload; formats without extra record
    /// kinds should bail from the callback.
    pub fn decode_transaction(
        &self,
        transaction: &Transaction,
        mut extra: impl FnMut(u8, &[u8]) -> anyhow::Result<()>,
    ) -> anyhow::Result<Vec<u8>> {
        let label = self.label;
        let mut metadata: Option<(u16, u32, sha256::Hash)> = None;
        let mut chunks: Vec<(u16, Vec<u8>)> = Vec::new();
        let mut seen_records = false;

        for output in &transaction.output {
            let Some((payload, has_extra_pushes)) = op_return_payload(&output.script_pubkey) else {
                continue;
            };
            if payload.len() < RECORD_HEADER_LEN || &payload[..MAGIC_LEN] != self.magic {
                continue;
            }
            if has_extra_pushes {
                anyhow::bail!("{label} OP_RETURN output contains extra pushes");
            }
            if payload[MAGIC_LEN] != self.version {
                anyhow::bail!("unsupported {label} encoding version");
            }
            seen_records = true;

            let kind = payload[MAGIC_LEN + 1];
            if kind == self.metadata_kind {
                if payload.len() != METADATA_LEN {
                    anyhow::bail!("invalid {label} metadata record length");
                }
                let next_metadata = (
                    u16::from_be_bytes(
                        payload[RECORD_HEADER_LEN..METADATA_TOTAL_LEN_OFFSET]
                            .try_into()
                            .expect("slice length is checked by METADATA_LEN"),
                    ),
                    u32::from_be_bytes(
                        payload[METADATA_TOTAL_LEN_OFFSET..METADATA_CHECKSUM_OFFSET]
                            .try_into()
                            .expect("slice length is checked by METADATA_LEN"),
                    ),
                    sha256::Hash::from_slice(&payload[METADATA_CHECKSUM_OFFSET..METADATA_LEN])?,
                );
                if metadata.replace(next_metadata).is_some() {
                    anyhow::bail!("duplicate {label} metadata record");
                }
            } else if kind == self.chunk_kind {
                if payload.len() < CHUNK_DATA_OFFSET {
                    anyhow::bail!("truncated {label} chunk record");
                }
                chunks.push((
                    u16::from_be_bytes(
                        payload[RECORD_HEADER_LEN..CHUNK_DATA_OFFSET]
                            .try_into()
                            .expect("slice length is checked by CHUNK_DATA_OFFSET"),
                    ),
                    payload[CHUNK_DATA_OFFSET..].to_vec(),
                ));
            } else {
                extra(kind, payload)?;
            }
        }

        if !seen_records {
            anyhow::bail!("transaction does not contain {label} records");
        }

        let (total_chunks, total_len, checksum) =
            metadata.ok_or_else(|| anyhow::anyhow!("missing {label} metadata record"))?;
        if total_chunks == 0 {
            anyhow::bail!("{label} chunk count can not be zero");
        }

        let mut ordered = vec![None; usize::from(total_chunks)];
        for (index, chunk) in chunks {
            let index = usize::from(index);
            if index >= ordered.len() {
                anyhow::bail!("{label} chunk index is out of bounds");
            }
            if ordered[index].replace(chunk).is_some() {
                anyhow::bail!("duplicate {label} chunk");
            }
        }

        let mut data = Vec::with_capacity(usize::try_from(total_len)?);
        for (index, chunk) in ordered.into_iter().enumerate() {
            let chunk = chunk.ok_or_else(|| anyhow::anyhow!("missing {label} chunk {index}"))?;
            data.extend_from_slice(&chunk);
        }
        if data.len() != usize::try_from(total_len)? {
            anyhow::bail!("decoded {label} length mismatch");
        }
        if sha256::Hash::hash(&data) != checksum {
            anyhow::bail!("decoded {label} checksum mismatch");
        }

        Ok(data)
    }

    /// Wrap one record payload into a zero-value `OP_RETURN` output.
    #[must_use]
    pub fn record_output(payload: &[u8], carrier_asset: AssetId) -> Output {
        debug_assert!(payload.len() <= MAX_OP_RETURN_PAYLOAD_BYTES);
        Output::new_explicit(Script::new_op_return(payload), 0, carrier_asset, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplicityhl::elements::{LockTime, TxOut, TxOutWitness, confidential};

    const TEST_FRAMING: RecordFraming = RecordFraming {
        magic: b"TESTMAGC",
        version: 1,
        metadata_kind: 0,
        chunk_kind: 2,
        label: "test payload",
    };

    // The record layout is a stable wire format; these bytes must never change.
    #[test]
    fn encode_payload_produces_stable_record_bytes() -> anyhow::Result<()> {
        let data = vec![0xab; 64];
        let records = TEST_FRAMING.encode_payload(&data)?;

        assert_eq!(records.len(), 3);

        let metadata = &records[0];
        assert_eq!(metadata.len(), 48);
        assert_eq!(&metadata[..10], b"TESTMAGC\x01\x00");
        assert_eq!(metadata[10..12], 2_u16.to_be_bytes());
        assert_eq!(metadata[12..16], 64_u32.to_be_bytes());
        assert_eq!(&metadata[16..48], sha256::Hash::hash(&data).as_byte_array());

        assert_eq!(records[1].len(), MAX_OP_RETURN_PAYLOAD_BYTES);
        assert_eq!(&records[1][..10], b"TESTMAGC\x01\x02");
        assert_eq!(records[1][10..12], 0_u16.to_be_bytes());
        assert_eq!(&records[1][12..], &data[..MAX_CHUNK_DATA_BYTES]);

        assert_eq!(&records[2][..10], b"TESTMAGC\x01\x02");
        assert_eq!(records[2][10..12], 1_u16.to_be_bytes());
        assert_eq!(&records[2][12..], &data[MAX_CHUNK_DATA_BYTES..]);

        Ok(())
    }

    #[test]
    fn decode_transaction_reassembles_out_of_order_chunks() -> anyhow::Result<()> {
        let data = (0..=255_u8).cycle().take(200).collect::<Vec<_>>();
        let mut records = TEST_FRAMING.encode_payload(&data)?;
        records.reverse();

        let transaction = Transaction {
            version: 2,
            lock_time: LockTime::ZERO,
            input: Vec::new(),
            output: records
                .iter()
                .map(|record| TxOut {
                    asset: confidential::Asset::Null,
                    value: confidential::Value::Null,
                    nonce: confidential::Nonce::Null,
                    script_pubkey: Script::new_op_return(record),
                    witness: TxOutWitness::default(),
                })
                .collect(),
        };

        let decoded = TEST_FRAMING.decode_transaction(&transaction, |_, _| {
            anyhow::bail!("unsupported test payload record type")
        })?;

        assert_eq!(decoded, data);

        Ok(())
    }
}
