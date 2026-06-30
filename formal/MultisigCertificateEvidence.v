From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import
  MultisigCertificateChecks MultisigCertificateCore
  MultisigCertificateProperties MultisigCertificateShape SimplicityByteDecoder
  TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Theorem check_compiled_multisig_byte_certificate_decode_evidence :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    CompiledMultisigByteCertificateDecodeEvidence certificate program.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [Hshape Hdecode].
  constructor.
  - apply certificate_shape_well_formed_sound. exact Hshape.
  - exact Hdecode.
  - eapply decode_structural_program_bytes_raw_program.
    exact Hdecode.
  - eapply decode_structural_program_bytes_hidden_cmrs_unique.
    exact Hdecode.
  - eapply decode_structural_program_bytes_hidden_cmrs_256.
    exact Hdecode.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_jets_are_multisig_subset.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_dag_well_formed.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_dag_len_bound.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_child_references.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_no_fail.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_no_disconnect1.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_without_cmr_closed_padding.
    exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_decode_evidence :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    CompiledMultisigByteCertificateStreamingDecodeEvidence
      certificate program.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [Hshape Hdecode].
  constructor.
  - apply certificate_shape_well_formed_sound. exact Hshape.
  - exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_raw_program.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_hidden_cmrs_unique.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_hidden_cmrs_256.
    exact Hdecode.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_jets_are_multisig_subset.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_dag_well_formed.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_dag_len_bound.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_child_references.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_no_fail.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_no_disconnect1.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_closed_padding.
    exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_bridge_evidence :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate_streaming alg certificate =
      Some program ->
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg certificate program.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_sound_with_static_fields
      alg certificate program Hcheck)
    as [Hstatic [Hdecode [Hcmr Hcmr_length]]].
  constructor.
  - exact Hstatic.
  - exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_raw_program.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_hidden_cmrs_unique.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_hidden_cmrs_256.
    exact Hdecode.
  - exact Hcmr.
  - exact Hcmr_length.
  - apply structural_program_jets_are_multisig_subset.
  - eapply decode_structural_program_bytes_streaming_dag_well_formed.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_dag_len_bound.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_child_references.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_no_fail.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_no_disconnect1.
    exact Hdecode.
  - eapply decode_structural_program_bytes_streaming_closed_padding.
    exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_bridge_evidence :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    CompiledMultisigByteCertificateBridgeEvidence alg certificate program.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound_with_static_fields
      alg certificate program Hcheck)
    as [Hstatic [Hdecode [Hcmr Hcmr_length]]].
  constructor.
  - exact Hstatic.
  - exact Hdecode.
  - eapply decode_structural_program_bytes_raw_program.
    exact Hdecode.
  - eapply decode_structural_program_bytes_hidden_cmrs_unique.
    exact Hdecode.
  - eapply decode_structural_program_bytes_hidden_cmrs_256.
    exact Hdecode.
  - exact Hcmr.
  - exact Hcmr_length.
  - eapply check_compiled_multisig_byte_certificate_jets_are_multisig_subset.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_dag_well_formed.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_dag_len_bound.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_child_references.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_no_fail.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_no_disconnect1.
    exact Hcheck.
  - eapply check_compiled_multisig_byte_certificate_closed_padding.
    exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_typed_bridge_evidence :
  forall alg hooks certificate program types root_arrow,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    check_typed_structural_program hooks program types root_arrow = true ->
    TypedCompiledMultisigByteCertificateBridgeEvidence
      alg hooks certificate program types root_arrow.
Proof.
  intros alg hooks certificate program types root_arrow Hcheck Htyped.
  constructor.
  - apply check_compiled_multisig_byte_certificate_bridge_evidence.
    exact Hcheck.
  - apply check_typed_structural_program_with_byte_evidence.
    + eapply check_compiled_multisig_byte_certificate_dag_well_formed.
      exact Hcheck.
    + eapply check_compiled_multisig_byte_certificate_no_fail.
      exact Hcheck.
    + eapply check_compiled_multisig_byte_certificate_no_disconnect1.
      exact Hcheck.
    + exact Htyped.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_typed_bridge_evidence :
  forall alg hooks certificate program types root_arrow,
    check_compiled_multisig_byte_certificate_streaming alg certificate =
      Some program ->
    check_typed_structural_program hooks program types root_arrow = true ->
    TypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg hooks certificate program types root_arrow.
Proof.
  intros alg hooks certificate program types root_arrow Hcheck Htyped.
  constructor.
  - apply check_compiled_multisig_byte_certificate_streaming_bridge_evidence.
    exact Hcheck.
  - apply check_typed_structural_program_with_byte_evidence.
    + pose proof
        (@check_compiled_multisig_byte_certificate_streaming_sound
          alg certificate program Hcheck)
        as [_ [Hdecode _]].
      eapply decode_structural_program_bytes_streaming_dag_well_formed.
      exact Hdecode.
    + pose proof
        (@check_compiled_multisig_byte_certificate_streaming_sound
          alg certificate program Hcheck)
        as [_ [Hdecode _]].
      eapply decode_structural_program_bytes_streaming_no_fail.
      exact Hdecode.
    + pose proof
        (@check_compiled_multisig_byte_certificate_streaming_sound
          alg certificate program Hcheck)
        as [_ [Hdecode _]].
      eapply decode_structural_program_bytes_streaming_no_disconnect1.
      exact Hdecode.
    + exact Htyped.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_typed_decode_evidence :
  forall hooks certificate program types root_arrow,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    check_typed_structural_program hooks program types root_arrow = true ->
    TypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      hooks certificate program types root_arrow.
Proof.
  intros hooks certificate program types root_arrow Hcheck Htyped.
  constructor.
  - apply check_compiled_multisig_byte_certificate_streaming_decode_evidence.
    exact Hcheck.
  - apply check_typed_structural_program_with_byte_evidence.
    + eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_dag_well_formed.
      exact Hcheck.
    + eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_no_fail.
      exact Hcheck.
    + eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_no_disconnect1.
      exact Hcheck.
    + exact Htyped.
Qed.

Theorem compiled_multisig_byte_certificate_streaming_decode_evidence_typed :
  forall hooks certificate program types root_arrow,
    CompiledMultisigByteCertificateStreamingDecodeEvidence
      certificate program ->
    check_typed_structural_program hooks program types root_arrow = true ->
    TypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      hooks certificate program types root_arrow.
Proof.
  intros hooks certificate program types root_arrow Hbytes Htyped.
  constructor.
  - exact Hbytes.
  - apply check_typed_structural_program_with_byte_evidence.
    + exact (streaming_decode_dag_well_formed Hbytes).
    + exact (streaming_decode_no_fail Hbytes).
    + exact (streaming_decode_no_disconnect1 Hbytes).
    + exact Htyped.
Qed.
