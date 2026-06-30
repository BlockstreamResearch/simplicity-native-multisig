From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import
  MultisigCertificateCore MultisigCertificateShape MultisigSourceBlocks
  SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Theorem check_compiled_multisig_byte_certificate_sound :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    certificate_shape_well_formed certificate = true /\
    decode_structural_program_bytes (cert_program_bytes certificate) =
      Some program /\
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits certificate) /\
    length (certificate_cmr_bits certificate) = 256.
Proof.
  intros alg certificate program Hcheck.
  unfold check_compiled_multisig_byte_certificate in Hcheck.
  destruct (certificate_shape_well_formed certificate) eqn:Hshape;
    [| discriminate].
  pose proof
    (@decode_structural_program_bytes_with_checked_cmr_sound
      alg
      (cert_program_bytes certificate)
      (certificate_cmr_bits certificate)
      program
      Hcheck)
    as [Hdecode [Hcmr Hcmr_length]].
  repeat split; assumption.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_sound :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate_streaming alg certificate =
      Some program ->
    certificate_shape_well_formed certificate = true /\
    decode_structural_program_bytes_streaming
      (cert_program_bytes certificate) =
      Some program /\
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits certificate) /\
    length (certificate_cmr_bits certificate) = 256.
Proof.
  intros alg certificate program Hcheck.
  unfold check_compiled_multisig_byte_certificate_streaming in Hcheck.
  destruct (certificate_shape_well_formed certificate) eqn:Hshape;
    [| discriminate].
  pose proof
    (@decode_structural_program_bytes_streaming_with_checked_cmr_sound
      alg
      (cert_program_bytes certificate)
      (certificate_cmr_bits certificate)
      program
      Hcheck)
    as [Hdecode [Hcmr Hcmr_length]].
  repeat split; assumption.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_sound :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    certificate_shape_well_formed certificate = true /\
    decode_structural_program_bytes (cert_program_bytes certificate) =
      Some program.
Proof.
  intros certificate program Hcheck.
  unfold check_compiled_multisig_byte_certificate_without_cmr in Hcheck.
  destruct (certificate_shape_well_formed certificate) eqn:Hshape;
    [| discriminate].
  split.
  - reflexivity.
  - exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_sound :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    certificate_shape_well_formed certificate = true /\
    decode_structural_program_bytes_streaming
      (cert_program_bytes certificate) =
      Some program.
Proof.
  intros certificate program Hcheck.
  unfold check_compiled_multisig_byte_certificate_streaming_without_cmr
    in Hcheck.
  destruct (certificate_shape_well_formed certificate) eqn:Hshape;
    [| discriminate].
  split.
  - reflexivity.
  - exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_without_cmr_static_fields :
  forall certificate program,
    check_compiled_multisig_byte_certificate_without_cmr certificate =
      Some program ->
    certificate_static_fields_well_formed certificate.
Proof.
  intros certificate program Hcheck.
  apply certificate_shape_well_formed_sound.
  pose proof
    (@check_compiled_multisig_byte_certificate_without_cmr_sound
      certificate program Hcheck)
    as [Hshape _].
  exact Hshape.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_static_fields :
  forall certificate program,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    certificate_static_fields_well_formed certificate.
Proof.
  intros certificate program Hcheck.
  apply certificate_shape_well_formed_sound.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
      certificate program Hcheck)
    as [Hshape _].
  exact Hshape.
Qed.

Theorem check_compiled_multisig_byte_certificate_static_fields :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    certificate_static_fields_well_formed certificate.
Proof.
  intros alg certificate program Hcheck.
  apply certificate_shape_well_formed_sound.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [Hshape _].
  exact Hshape.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_static_fields :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate_streaming alg certificate =
      Some program ->
    certificate_static_fields_well_formed certificate.
Proof.
  intros alg certificate program Hcheck.
  apply certificate_shape_well_formed_sound.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_sound
      alg certificate program Hcheck)
    as [Hshape _].
  exact Hshape.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_without_cmr_source_static_fields :
  forall certificate program participant1 participant2 participant3,
    check_compiled_multisig_byte_certificate_streaming_without_cmr certificate =
      Some program ->
    cert_participants certificate =
      [participant1; participant2; participant3] ->
    @static_parameter_checks_succeed
      (list byte)
      bytes_eqb
      (cert_threshold certificate)
      participant1
      participant2
      participant3.
Proof.
  intros certificate program participant1 participant2 participant3
    Hcheck Hparticipants.
  eapply certificate_static_fields_imply_source_static_parameter_checks.
  - exact Hparticipants.
  - eapply check_compiled_multisig_byte_certificate_streaming_without_cmr_static_fields.
    exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_source_static_fields :
  forall alg certificate program participant1 participant2 participant3,
    check_compiled_multisig_byte_certificate_streaming alg certificate =
      Some program ->
    cert_participants certificate =
      [participant1; participant2; participant3] ->
    @static_parameter_checks_succeed
      (list byte)
      bytes_eqb
      (cert_threshold certificate)
      participant1
      participant2
      participant3.
Proof.
  intros alg certificate program participant1 participant2 participant3
    Hcheck Hparticipants.
  eapply certificate_static_fields_imply_source_static_parameter_checks.
  - exact Hparticipants.
  - eapply check_compiled_multisig_byte_certificate_streaming_static_fields.
    exact Hcheck.
Qed.

Theorem check_compiled_multisig_byte_certificate_sound_with_static_fields :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate alg certificate = Some program ->
    certificate_static_fields_well_formed certificate /\
    decode_structural_program_bytes (cert_program_bytes certificate) =
      Some program /\
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits certificate) /\
    length (certificate_cmr_bits certificate) = 256.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_sound
      alg certificate program Hcheck)
    as [Hshape [Hdecode [Hcmr Hcmr_length]]].
  split.
  - apply certificate_shape_well_formed_sound. exact Hshape.
  - repeat split; assumption.
Qed.

Theorem check_compiled_multisig_byte_certificate_streaming_sound_with_static_fields :
  forall alg certificate program,
    check_compiled_multisig_byte_certificate_streaming alg certificate =
      Some program ->
    certificate_static_fields_well_formed certificate /\
    decode_structural_program_bytes_streaming
      (cert_program_bytes certificate) =
      Some program /\
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits certificate) /\
    length (certificate_cmr_bits certificate) = 256.
Proof.
  intros alg certificate program Hcheck.
  pose proof
    (@check_compiled_multisig_byte_certificate_streaming_sound
      alg certificate program Hcheck)
    as [Hshape [Hdecode [Hcmr Hcmr_length]]].
  split.
  - apply certificate_shape_well_formed_sound. exact Hshape.
  - repeat split; assumption.
Qed.
