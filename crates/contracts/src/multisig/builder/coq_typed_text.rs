pub(super) fn write_coq_typed_certificate_definition(module: &mut String) {
    module.push_str(
        r"Definition compiled_multisig_typed_certificate : option CompiledMultisigTypedByteCertificate :=
  expand_compact_typed_certificate compiled_multisig_compact_typed_certificate.

",
    );
}

pub(super) fn write_coq_typed_translation_theorems(module: &mut String) {
    module.push_str(
        r"Example compiled_multisig_typed_certificate_expands :
  match compiled_multisig_typed_certificate with
  | Some _ => true
  | None => false
  end = true.
Proof.
  lazy.
  reflexivity.
Qed.

Example compiled_multisig_compact_type_defs_atom_free :
  compact_bridge_type_defs_atom_free
    (compact_bridge_type_defs compiled_multisig_compact_typed_certificate) =
    true.
Proof.
  lazy.
  reflexivity.
Qed.

Theorem compiled_multisig_typed_certificate_atom_free :
  forall typed_certificate,
    compiled_multisig_typed_certificate = Some typed_certificate ->
    typed_byte_certificate_atom_free typed_certificate = true.
Proof.
  intros typed_certificate Hexpanded.
  unfold compiled_multisig_typed_certificate in Hexpanded.
  eapply expand_compact_typed_certificate_atom_free.
  - exact compiled_multisig_compact_type_defs_atom_free.
  - exact Hexpanded.
Qed.

Theorem compiled_multisig_typed_certificate_translates_to_core_type_algebra :
  forall A (alg : CoreTypeAlgebra A),
    exists typed_certificate translated_types translated_root,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      translate_typed_byte_certificate_types alg typed_certificate =
        Some (translated_types, translated_root).
Proof.
  intros A alg.
  pose proof compiled_multisig_typed_certificate_expands as His_some.
  destruct compiled_multisig_typed_certificate as [typed_certificate |]
    eqn:Hexpanded; [| discriminate].
  destruct
    (@translate_typed_byte_certificate_types_if_atom_free
      A alg typed_certificate)
    as [translated_types [translated_root Htranslated]].
  {
    eapply compiled_multisig_typed_certificate_atom_free.
    exact Hexpanded.
  }
  exists typed_certificate, translated_types, translated_root.
  split.
  - reflexivity.
  - exact Htranslated.
Qed.

",
    );
}

pub(super) fn write_coq_typed_program_definitions(module: &mut String) {
    module.push_str(
        r"Definition compiled_multisig_streaming_typed_decoded_program : option StructuralProgram :=
  check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
    reject_unhandled_type_hooks compiled_multisig_compact_typed_certificate.

Example compiled_multisig_streaming_typed_decoded_program_is_some :
  match compiled_multisig_streaming_typed_decoded_program with
  | Some _ => true
  | None => false
  end = true.
Proof.
  lazy.
  reflexivity.
Qed.

Definition compiled_multisig_type_check_for_program
    (program : StructuralProgram) : bool :=
  match compiled_multisig_typed_certificate with
  | Some typed_certificate =>
      check_typed_structural_program
        (typed_certificate_hooks reject_unhandled_type_hooks)
        program
        (typed_certificate_types typed_certificate)
        (typed_certificate_root_arrow typed_certificate)
  | None => false
  end.

Definition compiled_multisig_streaming_typed_checked_program
    (alg : CmrAlgebra)
    (base_hooks : TypeHooks) : option StructuralProgram :=
  check_compiled_multisig_compact_typed_byte_certificate_streaming
    alg base_hooks compiled_multisig_compact_typed_certificate.

",
    );
}

pub(super) fn write_coq_typed_decode_evidence(module: &mut String) {
    module.push_str(
        r"Theorem compiled_multisig_streaming_typed_decode_evidence :
  exists program,
    compiled_multisig_streaming_typed_decoded_program = Some program /\
    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      reject_unhandled_type_hooks
      compiled_multisig_compact_typed_certificate
      program.
Proof.
  pose proof compiled_multisig_streaming_typed_decoded_program_is_some
    as His_some.
  unfold compiled_multisig_streaming_typed_decoded_program in His_some |- *.
  destruct (check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
    reject_unhandled_type_hooks
    compiled_multisig_compact_typed_certificate) as [program|] eqn:Hdecoded.
  - exists program. split.
    + reflexivity.
    + eapply check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr_evidence.
      exact Hdecoded.
  - discriminate His_some.
Qed.

Theorem compiled_multisig_streaming_typed_decode_evidence_if_checked :
  forall program,
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      reject_unhandled_type_hooks
      compiled_multisig_compact_typed_certificate
      program.
Proof.
  intros program Hdecoded.
  unfold compiled_multisig_streaming_typed_decoded_program in Hdecoded.
  exact (@check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr_evidence
    reject_unhandled_type_hooks
    compiled_multisig_compact_typed_certificate
    program
    Hdecoded).
Qed.

Theorem compiled_multisig_streaming_typed_bridge_evidence_from_cmr_if_checked :
  forall alg program,
    CmrAlgebraWellFormed alg ->
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits compiled_multisig_certificate) ->
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg
      reject_unhandled_type_hooks
      compiled_multisig_compact_typed_certificate
      program.
Proof.
  intros alg program Halg Hdecoded Hcmr.
  eapply compact_typed_byte_certificate_streaming_bridge_evidence_from_decode_and_cmr.
  - exact Halg.
  - eapply compiled_multisig_streaming_typed_decode_evidence_if_checked.
    exact Hdecoded.
  - exact Hcmr.
Qed.

Theorem compiled_multisig_streaming_typed_decode_evidence_from_byte_evidence_if_type_checked :
  forall program,
    CompiledMultisigByteCertificateStreamingDecodeEvidence
      compiled_multisig_certificate
      program ->
    compiled_multisig_type_check_for_program program = true ->
    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      reject_unhandled_type_hooks
      compiled_multisig_compact_typed_certificate
      program.
Proof.
  intros program Hbytes Htyped.
  unfold compiled_multisig_type_check_for_program in Htyped.
  unfold compiled_multisig_typed_certificate in Htyped.
  destruct (expand_compact_typed_certificate
              compiled_multisig_compact_typed_certificate)
    as [typed_certificate |] eqn:Hexpand; [| discriminate].
  eapply compact_typed_byte_certificate_streaming_decode_evidence_from_byte_evidence.
  - exact Hexpand.
  - exact Hbytes.
  - exact Htyped.
Qed.

",
    );
}

pub(super) fn write_coq_typed_bridge_evidence(module: &mut String) {
    module.push_str(
        r"Theorem compiled_multisig_streaming_typed_bridge_evidence_if_checked :
  forall alg base_hooks program,
    compiled_multisig_streaming_typed_checked_program
      alg base_hooks = Some program ->
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg
      base_hooks
      compiled_multisig_compact_typed_certificate
      program.
Proof.
  intros alg base_hooks program Hchecked.
  unfold compiled_multisig_streaming_typed_checked_program in Hchecked.
  exact
    (@check_compiled_multisig_compact_typed_byte_certificate_streaming_evidence
      alg
      base_hooks
      compiled_multisig_compact_typed_certificate
      program
      Hchecked).
Qed.

Theorem compiled_multisig_streaming_typed_checked_byte_bridge_evidence_if_checked :
  forall alg base_hooks program,
    compiled_multisig_streaming_typed_checked_program
      alg base_hooks = Some program ->
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg compiled_multisig_certificate program.
Proof.
  intros alg base_hooks program Hchecked.
  change
    (CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg
      (compact_typed_certificate_bytes
        compiled_multisig_compact_typed_certificate)
      program).
  eapply
    (@compact_typed_byte_certificate_streaming_bridge_byte_evidence
      alg
      base_hooks
      compiled_multisig_compact_typed_certificate
      program).
  eapply compiled_multisig_streaming_typed_bridge_evidence_if_checked.
  exact Hchecked.
Qed.

Theorem compiled_multisig_streaming_typed_checked_decoded_program :
  forall alg base_hooks program,
    compiled_multisig_streaming_typed_checked_program
      alg base_hooks = Some program ->
    decode_structural_program_bytes_streaming
      (cert_program_bytes compiled_multisig_certificate) =
      Some program.
Proof.
  intros alg base_hooks program Hchecked.
  pose proof
    (@compiled_multisig_streaming_typed_checked_byte_bridge_evidence_if_checked
      alg base_hooks program Hchecked) as Hbyte.
  exact (streaming_bridge_decoded_program Hbyte).
Qed.

Theorem compiled_multisig_streaming_typed_checked_cmr :
  forall alg base_hooks program,
    compiled_multisig_streaming_typed_checked_program
      alg base_hooks = Some program ->
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits compiled_multisig_certificate).
Proof.
  intros alg base_hooks program Hchecked.
  pose proof
    (@compiled_multisig_streaming_typed_checked_byte_bridge_evidence_if_checked
      alg base_hooks program Hchecked) as Hbyte.
  exact (streaming_bridge_checked_cmr Hbyte).
Qed.
",
    );
}
