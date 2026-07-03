use std::fmt::Write as _;

use super::{CompiledMultisigCertificate, PARTICIPANT_COUNT};

impl CompiledMultisigCertificate {
    /// Coq data module containing this certificate as checked constants.
    ///
    /// The generated module is ONLY data: threshold, participant public keys,
    /// no-witness program bytes, and CMR bytes, matching the checked-in
    /// `formal/CompiledMultisigByteData.v`.  Definitions, checker runs, and
    /// theorems over this data live in the hand-maintained formal tree
    /// (`CompiledMultisigExampleCore.v`, `CompiledMultisigExample.v`,
    /// `CompiledMultisigTypedExample.v`, ...), which imports this module.
    /// The exporter intentionally emits no proof text: proofs are living Coq
    /// code and regenerating them from Rust string constants would silently
    /// revert audited proof engineering.
    #[must_use]
    pub fn coq_certificate_module(&self) -> String {
        let mut module = String::new();

        writeln!(module, "From Coq Require Import List.").expect("writing to a String cannot fail");
        writeln!(
            module,
            "From MultisigFormal Require Import SimplicityByteDecoder MultisigCertificate."
        )
        .expect("writing to a String cannot fail");
        module.push_str("\nImport ListNotations.\n\n");

        writeln!(
            module,
            "Definition compiled_multisig_certificate : CompiledMultisigByteCertificate := {{|"
        )
        .expect("writing to a String cannot fail");
        let threshold = self.parameters.threshold();
        writeln!(module, "  cert_threshold := {threshold};")
            .expect("writing to a String cannot fail");
        writeln!(module, "  cert_participants := [").expect("writing to a String cannot fail");

        for (index, participant) in self.parameters.participants().into_iter().enumerate() {
            let terminator = if index + 1 == PARTICIPANT_COUNT {
                ""
            } else {
                ";"
            };
            let participant_bytes = coq_byte_list(participant.serialize());
            writeln!(module, "    {participant_bytes}{terminator}")
                .expect("writing to a String cannot fail");
        }

        writeln!(module, "  ];").expect("writing to a String cannot fail");
        let program_bytes = coq_byte_list(self.program_bytes.iter().copied());
        writeln!(module, "  cert_program_bytes := {program_bytes};")
            .expect("writing to a String cannot fail");
        let cmr_bytes = coq_byte_list(self.cmr.as_ref().iter().copied());
        writeln!(module, "  cert_cmr_bytes := {cmr_bytes}")
            .expect("writing to a String cannot fail");
        module.push_str("|}.\n");

        module
    }
}

pub(super) fn coq_byte_list(bytes: impl IntoIterator<Item = u8>) -> String {
    const MAX_INLINE_BYTES: usize = 64;
    const CHUNK_BYTES: usize = 32;

    let bytes = bytes.into_iter().collect::<Vec<_>>();

    if bytes.len() <= MAX_INLINE_BYTES {
        return coq_byte_chunk(&bytes);
    }

    let mut list = String::from("(\n");
    let chunk_count = bytes.chunks(CHUNK_BYTES).len();

    for (index, chunk) in bytes.chunks(CHUNK_BYTES).enumerate() {
        list.push_str("    ");
        list.push_str(&coq_byte_chunk(chunk));
        if index + 1 != chunk_count {
            list.push_str(" ++");
        }
        list.push('\n');
    }

    list.push_str("  )");
    list
}

fn coq_byte_chunk(bytes: &[u8]) -> String {
    let mut list = String::from("[");

    for (index, byte) in bytes.iter().copied().enumerate() {
        if index != 0 {
            list.push_str("; ");
        }
        write!(list, "{byte}").expect("writing to a String cannot fail");
    }

    list.push(']');
    list
}
