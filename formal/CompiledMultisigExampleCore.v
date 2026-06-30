From Coq Require Import List.
From MultisigFormal Require Import
  SimplicityByteDecoder MultisigCertificate MultisigSecurity MultisigSourceBlocks
  CompiledMultisigByteData.

Import ListNotations.

Definition compiled_multisig_decoded_program : option StructuralProgram :=
  check_compiled_multisig_byte_certificate_without_cmr
    compiled_multisig_certificate.

Definition compiled_multisig_streaming_decoded_program : option StructuralProgram :=
  check_compiled_multisig_byte_certificate_streaming_without_cmr
    compiled_multisig_certificate.

Definition compiled_multisig_streaming_checked_program
    (alg : CmrAlgebra) : option StructuralProgram :=
  check_compiled_multisig_byte_certificate_streaming
    alg compiled_multisig_certificate.

Definition compiled_multisig_streaming_raw_program :=
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

Example compiled_multisig_streaming_decoded_program_is_some :
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

Theorem compiled_multisig_streaming_source_static_fields :
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

Definition compiled_multisig_threshold : nat :=
  cert_threshold compiled_multisig_certificate.

Definition compiled_multisig_participant1 : list byte :=
  nth 0 (cert_participants compiled_multisig_certificate) [].

Definition compiled_multisig_participant2 : list byte :=
  nth 1 (cert_participants compiled_multisig_certificate) [].

Definition compiled_multisig_participant3 : list byte :=
  nth 2 (cert_participants compiled_multisig_certificate) [].

Definition compiled_multisig_participants : list (list byte) :=
  [compiled_multisig_participant1;
   compiled_multisig_participant2;
   compiled_multisig_participant3].

Theorem compiled_multisig_certificate_static_parameter_checks :
  @static_parameter_checks_succeed
    (list byte)
    bytes_eqb
    compiled_multisig_threshold
    compiled_multisig_participant1
    compiled_multisig_participant2
    compiled_multisig_participant3.
Proof.
  destruct compiled_multisig_streaming_source_static_fields
    as [program [participant1 [participant2 [participant3
         [_ [Hparticipants Hstatic]]]]]].
  unfold compiled_multisig_threshold.
  unfold compiled_multisig_participant1, compiled_multisig_participant2,
    compiled_multisig_participant3.
  assert (Hparticipant1 :
    nth 0 (cert_participants compiled_multisig_certificate) [] =
      participant1).
  {
    rewrite Hparticipants.
    reflexivity.
  }
  assert (Hparticipant2 :
    nth 1 (cert_participants compiled_multisig_certificate) [] =
      participant2).
  {
    rewrite Hparticipants.
    reflexivity.
  }
  assert (Hparticipant3 :
    nth 2 (cert_participants compiled_multisig_certificate) [] =
      participant3).
  {
    rewrite Hparticipants.
    reflexivity.
  }
  rewrite Hparticipant1, Hparticipant2, Hparticipant3.
  exact Hstatic.
Qed.
