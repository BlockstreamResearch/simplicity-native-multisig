use super::{MultisigParameters, PARTICIPANT_COUNT};

use simplicityhl::simplicity::Cmr;
use simplicityhl::simplicity::types::arrow::FinalArrow;

/// Static certificate for one compiled multisig covenant instance.
///
/// The byte vector is the canonical no-witness Simplicity encoding of the
/// committed program.  The CMR is computed from the same `CommitNode`, so this
/// object is the Rust-side artifact that the Coq byte decoder should consume.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompiledMultisigCertificate {
    pub(super) parameters: MultisigParameters,
    pub(super) cmr: Cmr,
    pub(super) program_bytes: Vec<u8>,
    pub(super) type_table: Vec<Option<FinalArrow>>,
    pub(super) root_arrow: FinalArrow,
}

/// Stable serializable form of [`CompiledMultisigCertificate`].
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct CompiledMultisigCertificateArtifact {
    /// Signature threshold compiled into the program.
    pub threshold: u32,
    /// Participant x-only public keys in declaration order, hex encoded.
    pub participants_hex: [String; PARTICIPANT_COUNT],
    /// Commitment Merkle root, hex encoded.
    pub cmr_hex: String,
    /// Canonical no-witness Simplicity program bytes, hex encoded.
    pub program_hex: String,
}

impl CompiledMultisigCertificate {
    /// Stable serializable artifact for external proof tooling.
    #[must_use]
    pub fn artifact(&self) -> CompiledMultisigCertificateArtifact {
        CompiledMultisigCertificateArtifact {
            threshold: self.parameters.threshold(),
            participants_hex: self
                .parameters
                .participants()
                .map(|participant| hex::encode(participant.serialize())),
            cmr_hex: hex::encode(self.cmr.as_ref()),
            program_hex: hex::encode(&self.program_bytes),
        }
    }
}
