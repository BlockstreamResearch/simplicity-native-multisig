From Coq Require Import List Bool.
From MultisigFormal Require Import
  CmrWellFormed ElementsJetTypes MultisigCertificate
  MultisigTypedCertificateCore MultisigTypedCertificateEvidence
  SimplicityByteDecoder TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition reject_unhandled_type_hooks : TypeHooks := {|
  hook_jet_arrow := elements_jet_arrow;
  hook_witness_allowed := fun _ => false;
  hook_fail_allowed := fun _ _ => false;
  hook_word_allowed := fun _ _ _ => false;
  hook_disconnect1_allowed := fun _ _ => false;
  hook_disconnect_allowed := fun _ _ _ => false
|}.

Definition example_unit_typed_certificate :
    CompiledMultisigTypedByteCertificate := {|
  typed_certificate_bytes := example_unit_certificate;
  typed_certificate_types :=
    [Some {| bridge_source := BTUnit; bridge_target := BTUnit |}];
  typed_certificate_root_arrow :=
    {| bridge_source := BTUnit; bridge_target := BTUnit |}
|}.

Example example_unit_typed_certificate_streaming_checks :
  check_compiled_multisig_typed_byte_certificate_streaming
    zero_cmr_alg
    reject_unhandled_type_hooks
    example_unit_typed_certificate =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example example_unit_typed_certificate_streaming_without_cmr_checks :
  check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
    reject_unhandled_type_hooks
    example_unit_typed_certificate =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Definition example_unit_compact_typed_certificate :
    CompactCompiledMultisigTypedByteCertificate := {|
  compact_typed_certificate_bytes := example_unit_certificate;
  compact_bridge_type_defs := [CBTDUnit];
  compact_bridge_arrow_defs := [(0, 0)];
  compact_type_table_entries := [Some 0];
  compact_root_arrow_index := 0
|}.

Example example_unit_compact_typed_certificate_expands :
  expand_compact_typed_certificate
    example_unit_compact_typed_certificate =
    Some example_unit_typed_certificate.
Proof. reflexivity. Qed.

Example example_unit_compact_typed_certificate_streaming_checks :
  check_compiled_multisig_compact_typed_byte_certificate_streaming
    zero_cmr_alg
    reject_unhandled_type_hooks
    example_unit_compact_typed_certificate =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example example_unit_compact_typed_certificate_streaming_without_cmr_checks :
  check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
    reject_unhandled_type_hooks
    example_unit_compact_typed_certificate =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.
