From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import
  MultisigCertificateChecks MultisigCertificateCore SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.


Theorem check_compiled_multisig_byte_certificate_jets_are_multisig_subset :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    structural_program_uses_only_multisig_jets program.
Proof.
  intros alg certificate program _Hcheck.
  apply structural_program_jets_are_multisig_subset.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_jets_are_multisig_subset :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    structural_program_uses_only_multisig_jets program.
Proof.
  intros certificate program _Hcheck.
  apply structural_program_jets_are_multisig_subset.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_jets_are_multisig_subset :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    structural_program_uses_only_multisig_jets program.
Proof.
  intros certificate program _Hcheck.
  apply structural_program_jets_are_multisig_subset.
Qed.

Theorem check_compiled_multisig_byte_certificate_dag_well_formed :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    structural_program_dag_well_formed program = true.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [_ [Hdecode _]].
  eapply decode_structural_program_bytes_dag_well_formed.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_dag_well_formed :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    structural_program_dag_well_formed program = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_dag_well_formed.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_dag_well_formed :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    structural_program_dag_well_formed program = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_streaming_dag_well_formed.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_child_references :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [_ [Hdecode _]].
  eapply decode_structural_program_bytes_child_references.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_child_references :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_child_references.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_child_references :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_streaming_child_references.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_dag_len_bound :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    length (structural_nodes program) <= dag_len_max.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [_ [Hdecode _]].
  eapply decode_structural_program_bytes_dag_len_bound.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_dag_len_bound :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    length (structural_nodes program) <= dag_len_max.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_dag_len_bound.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_dag_len_bound :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    length (structural_nodes program) <= dag_len_max.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_streaming_dag_len_bound.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_no_fail :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    structural_program_no_fail program = true.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [_ [Hdecode _]].
  eapply decode_structural_program_bytes_no_fail.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_no_disconnect1 :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [_ [Hdecode _]].
  eapply decode_structural_program_bytes_no_disconnect1.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_no_fail :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    structural_program_no_fail program = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_no_fail.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_no_disconnect1 :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_no_disconnect1.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_no_fail :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    structural_program_no_fail program = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_streaming_no_fail.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_no_disconnect1 :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_streaming_no_disconnect1.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_closed_padding :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    program_bytes_closed_padding (cert_program_bytes certificate) = true.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [_ [Hdecode _]].
  eapply decode_structural_program_bytes_closed_padding.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_closed_padding :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    program_bytes_closed_padding (cert_program_bytes certificate) = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_closed_padding.
  exact Hdecode.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_closed_padding :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    program_bytes_streaming_closed_padding
      (cert_program_bytes certificate) = true.
Proof.
  intros certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [_ Hdecode].
  eapply decode_structural_program_bytes_streaming_closed_padding.
  exact Hdecode.
Qed.
