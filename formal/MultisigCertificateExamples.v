From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import
  MultisigCertificateCore MultisigCertificateEvidence SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition example_participant_1 : list byte := repeat 1 32.
Definition example_participant_2 : list byte := repeat 2 32.
Definition example_participant_3 : list byte := repeat 3 32.

Definition example_unit_certificate : CompiledMultisigByteCertificate := {|
  cert_threshold := 1;
  cert_participants :=
    [example_participant_1; example_participant_2; example_participant_3];
  cert_program_bytes := [36];
  cert_cmr_bytes := repeat 0 32
|}.

Example example_unit_certificate_shape :
  certificate_shape_well_formed example_unit_certificate = true.
Proof. reflexivity. Qed.

Example example_unit_certificate_checks :
  check_compiled_multisig_byte_certificate
    zero_cmr_alg
    example_unit_certificate =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example example_unit_certificate_streaming_checks :
  check_compiled_multisig_byte_certificate_streaming
    zero_cmr_alg
    example_unit_certificate =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example example_rejects_malformed_participant_count :
  check_compiled_multisig_byte_certificate
    zero_cmr_alg
    {|
      cert_threshold := 1;
      cert_participants := [example_participant_1; example_participant_2];
      cert_program_bytes := [36];
      cert_cmr_bytes := repeat 0 32
    |} =
    None.
Proof. reflexivity. Qed.

Example example_rejects_duplicate_participants :
  check_compiled_multisig_byte_certificate
    zero_cmr_alg
    {|
      cert_threshold := 1;
      cert_participants :=
        [example_participant_1; example_participant_2; example_participant_1];
      cert_program_bytes := [36];
      cert_cmr_bytes := repeat 0 32
    |} =
    None.
Proof. reflexivity. Qed.

Example example_rejects_malformed_cmr_bytes :
  check_compiled_multisig_byte_certificate
    zero_cmr_alg
    {|
      cert_threshold := 1;
      cert_participants :=
        [example_participant_1; example_participant_2; example_participant_3];
      cert_program_bytes := [36];
      cert_cmr_bytes := [0]
    |} =
    None.
Proof. reflexivity. Qed.
