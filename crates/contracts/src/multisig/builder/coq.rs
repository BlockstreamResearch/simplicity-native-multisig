use std::fmt::Write as _;

use super::coq_typed_text::{
    write_coq_typed_bridge_evidence, write_coq_typed_certificate_definition,
    write_coq_typed_decode_evidence, write_coq_typed_program_definitions,
    write_coq_typed_translation_theorems,
};
use super::coq_types::write_coq_type_artifact;
use super::{CompiledMultisigCertificate, PARTICIPANT_COUNT};

impl CompiledMultisigCertificate {
    /// Complete Coq module containing this certificate as checked constants.
    ///
    /// The generated module is only data: threshold, participant public keys,
    /// no-witness program bytes, and CMR bytes, plus decode-only checkers and
    /// theorems that turn successful decodes into byte-certificate evidence.
    /// The full formal bridge still has to import this module and run
    /// `check_compiled_multisig_byte_certificate` with the concrete CMR algebra
    /// so Coq decodes the bytes and checks the CMR path itself.
    #[must_use]
    pub fn coq_certificate_module(&self) -> String {
        coq_certificate_module(self, false)
    }

    /// Complete Coq module that also exports the per-node type table.
    ///
    /// This is intentionally separate from [`Self::coq_certificate_module`].
    /// The concrete multisig type table is emitted as compact type and arrow
    /// indexes; Coq expands that artifact before running the typed checker.
    #[must_use]
    pub fn coq_typed_certificate_module(&self) -> String {
        coq_certificate_module(self, true)
    }
}

fn coq_certificate_module(
    certificate: &CompiledMultisigCertificate,
    include_types: bool,
) -> String {
    let mut module = String::new();

    writeln!(module, "From Coq Require Import List.").expect("writing to a String cannot fail");
    if include_types {
        writeln!(
            module,
            "From MultisigFormal Require Import\n  BridgeTypeTranslation CmrWellFormed SimplicityByteDecoder TypedBridge\n  MultisigCertificate MultisigTypedCertificate MultisigSourceBlocks."
        )
        .expect("writing to a String cannot fail");
    } else {
        writeln!(
            module,
            "From MultisigFormal Require Import\n  SimplicityByteDecoder MultisigCertificate MultisigSourceBlocks."
        )
        .expect("writing to a String cannot fail");
    }
    module.push_str("\nImport ListNotations.\n\n");

    writeln!(
        module,
        "Definition compiled_multisig_certificate : CompiledMultisigByteCertificate := {{|"
    )
    .expect("writing to a String cannot fail");
    let threshold = certificate.parameters.threshold();
    writeln!(module, "  cert_threshold := {threshold};").expect("writing to a String cannot fail");
    writeln!(module, "  cert_participants := [").expect("writing to a String cannot fail");

    for (index, participant) in certificate
        .parameters
        .participants()
        .into_iter()
        .enumerate()
    {
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
    let program_bytes = coq_byte_list(certificate.program_bytes.iter().copied());
    writeln!(module, "  cert_program_bytes := {program_bytes};")
        .expect("writing to a String cannot fail");
    let cmr_bytes = coq_byte_list(certificate.cmr.as_ref().iter().copied());
    writeln!(module, "  cert_cmr_bytes := {cmr_bytes}").expect("writing to a String cannot fail");
    module.push_str("|}.\n\n");

    if include_types {
        write_coq_type_artifact(&mut module, certificate);
        write_coq_typed_certificate_definition(&mut module);
        write_coq_typed_translation_theorems(&mut module);
    }

    module.push_str(
        r"Definition compiled_multisig_decoded_program : option StructuralProgram :=
  check_compiled_multisig_byte_certificate_without_cmr
    compiled_multisig_certificate.

Definition compiled_multisig_streaming_decoded_program : option StructuralProgram :=
  check_compiled_multisig_byte_certificate_streaming_without_cmr
    compiled_multisig_certificate.

Definition compiled_multisig_streaming_checked_program
    (alg : CmrAlgebra) : option StructuralProgram :=
  check_compiled_multisig_byte_certificate_streaming
    alg compiled_multisig_certificate.

",
    );

    if include_types {
        write_coq_typed_program_definitions(&mut module);
    }

    module.push_str(
        r"Definition compiled_multisig_streaming_raw_program :=
  decode_program_bytes_streaming
    (cert_program_bytes compiled_multisig_certificate).

Example compiled_multisig_streaming_raw_program_is_some :
  match compiled_multisig_streaming_raw_program with
  | Some _ => true
  | None => false
  end = true.
Proof.
  lazy.
  reflexivity.
Qed.

Definition compiled_multisig_streaming_structural_program :=
  decode_structural_program_bytes_streaming
    (cert_program_bytes compiled_multisig_certificate).

Example compiled_multisig_streaming_structural_program_is_some :
  match compiled_multisig_streaming_structural_program with
  | Some _ => true
  | None => false
  end = true.
Proof.
  lazy.
  reflexivity.
Qed.

Theorem compiled_multisig_streaming_structural_program_exists :
  exists program,
    compiled_multisig_streaming_structural_program = Some program.
Proof.
  pose proof compiled_multisig_streaming_structural_program_is_some as His_some.
  destruct compiled_multisig_streaming_structural_program as [program|] eqn:Hdecoded.
  - exists program. reflexivity.
  - discriminate His_some.
Qed.

",
    );

    module.push_str(
        r"Example compiled_multisig_streaming_decoded_program_is_some :
  match compiled_multisig_streaming_decoded_program with
  | Some _ => true
  | None => false
  end = true.
Proof.
  lazy.
  reflexivity.
Qed.

Theorem compiled_multisig_streaming_decode_evidence :
  exists program,
    compiled_multisig_streaming_decoded_program = Some program /\
    CompiledMultisigByteCertificateStreamingDecodeEvidence
      compiled_multisig_certificate program.
Proof.
  pose proof compiled_multisig_streaming_decoded_program_is_some as His_some.
  unfold compiled_multisig_streaming_decoded_program in His_some |- *.
  destruct (check_compiled_multisig_byte_certificate_streaming_without_cmr
    compiled_multisig_certificate) as [program|] eqn:Hdecoded.
  - exists program. split.
    + reflexivity.
    + eapply check_compiled_multisig_byte_certificate_streaming_decode_evidence.
      exact Hdecoded.
  - discriminate His_some.
Qed.

",
    );

    module.push_str(
        r"Theorem compiled_multisig_streaming_source_static_fields :
  exists program participant1 participant2 participant3,
    compiled_multisig_streaming_decoded_program = Some program /\
    cert_participants compiled_multisig_certificate =
      [participant1; participant2; participant3] /\
    @static_parameter_checks_succeed
      (list byte)
      bytes_eqb
      (cert_threshold compiled_multisig_certificate)
      participant1
      participant2
      participant3.
Proof.
  destruct compiled_multisig_streaming_decode_evidence
    as [program [Hdecoded _]].
  pose proof Hdecoded as Hcheck.
  unfold compiled_multisig_streaming_decoded_program in Hcheck.
  exists program.
  exists (nth 0 (cert_participants compiled_multisig_certificate) []).
  exists (nth 1 (cert_participants compiled_multisig_certificate) []).
  exists (nth 2 (cert_participants compiled_multisig_certificate) []).
  split.
  - exact Hdecoded.
  - split.
    + reflexivity.
    + eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_source_static_fields.
      * exact Hcheck.
      * reflexivity.
Qed.

Theorem compiled_multisig_certificate_source_static_fields :
  exists program participant1 participant2 participant3,
    compiled_multisig_streaming_decoded_program = Some program /\
    cert_participants compiled_multisig_certificate =
      [participant1; participant2; participant3] /\
    @static_parameter_checks_succeed
      (list byte)
      bytes_eqb
      (cert_threshold compiled_multisig_certificate)
      participant1
      participant2
      participant3.
Proof.
  exact compiled_multisig_streaming_source_static_fields.
Qed.

",
    );

    if include_types {
        write_coq_typed_decode_evidence(&mut module);
    }

    module.push_str(
        r"Theorem compiled_multisig_streaming_bridge_evidence_if_checked_cmr :
  forall alg program,
    compiled_multisig_streaming_checked_program alg = Some program ->
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg compiled_multisig_certificate program.
Proof.
  intros alg program Hdecoded.
  unfold compiled_multisig_streaming_checked_program in Hdecoded.
  exact (@check_compiled_multisig_byte_certificate_streaming_bridge_evidence
    alg
    compiled_multisig_certificate
    program
    Hdecoded).
Qed.

",
    );

    if include_types {
        write_coq_typed_bridge_evidence(&mut module);
    }

    module.push_str(
        r"Theorem compiled_multisig_decode_evidence_if_some :
  forall program,
    check_compiled_multisig_byte_certificate_without_cmr
      compiled_multisig_certificate = Some program ->
    CompiledMultisigByteCertificateDecodeEvidence
      compiled_multisig_certificate program.
Proof.
  intros program Hdecoded.
  exact (@check_compiled_multisig_byte_certificate_decode_evidence
    compiled_multisig_certificate
    program
    Hdecoded).
Qed.
",
    );

    module
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
