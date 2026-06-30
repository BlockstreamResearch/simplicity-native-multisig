From Coq Require Import List Bool.
From MultisigFormal Require Import
  CmrWellFormed MultisigCertificate MultisigTypedCertificateCore
  SimplicityByteDecoder TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
    (base_hooks : TypeHooks)
    (certificate : CompiledMultisigTypedByteCertificate) :
    option StructuralProgram :=
  match check_compiled_multisig_byte_certificate_streaming_without_cmr
          (typed_certificate_bytes certificate) with
  | Some program =>
      if check_typed_structural_program
           (typed_certificate_hooks base_hooks)
           program
           (typed_certificate_types certificate)
           (typed_certificate_root_arrow certificate)
      then Some program
      else None
  | None => None
  end.

Definition check_compiled_multisig_typed_byte_certificate_streaming
    (alg : CmrAlgebra)
    (base_hooks : TypeHooks)
    (certificate : CompiledMultisigTypedByteCertificate) :
    option StructuralProgram :=
  match check_compiled_multisig_byte_certificate_streaming
          alg
          (typed_certificate_bytes certificate) with
  | Some program =>
      if check_typed_structural_program
           (typed_certificate_hooks base_hooks)
           program
           (typed_certificate_types certificate)
           (typed_certificate_root_arrow certificate)
      then Some program
      else None
  | None => None
  end.

Theorem check_compiled_multisig_typed_byte_certificate_streaming_sound :
  forall alg base_hooks certificate program,
    check_compiled_multisig_typed_byte_certificate_streaming
      alg base_hooks certificate = Some program ->
    check_compiled_multisig_byte_certificate_streaming
      alg (typed_certificate_bytes certificate) = Some program /\
    check_typed_structural_program
      (typed_certificate_hooks base_hooks)
      program
      (typed_certificate_types certificate)
      (typed_certificate_root_arrow certificate) = true.
Proof.
  intros alg base_hooks certificate program Hcheck.
  unfold check_compiled_multisig_typed_byte_certificate_streaming in Hcheck.
  destruct (check_compiled_multisig_byte_certificate_streaming
              alg (typed_certificate_bytes certificate))
    as [decoded_program |] eqn:Hdecoded; [| discriminate].
  destruct (check_typed_structural_program
              (typed_certificate_hooks base_hooks)
              decoded_program
              (typed_certificate_types certificate)
              (typed_certificate_root_arrow certificate))
    eqn:Htyped; [| discriminate].
  inversion Hcheck; subst decoded_program.
  split; assumption.
Qed.

Theorem check_compiled_multisig_typed_byte_certificate_streaming_without_cmr_sound :
  forall base_hooks certificate program,
    check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
      base_hooks certificate = Some program ->
    check_compiled_multisig_byte_certificate_streaming_without_cmr
      (typed_certificate_bytes certificate) = Some program /\
    check_typed_structural_program
      (typed_certificate_hooks base_hooks)
      program
      (typed_certificate_types certificate)
      (typed_certificate_root_arrow certificate) = true.
Proof.
  intros base_hooks certificate program Hcheck.
  unfold check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
    in Hcheck.
  destruct (check_compiled_multisig_byte_certificate_streaming_without_cmr
              (typed_certificate_bytes certificate))
    as [decoded_program |] eqn:Hdecoded; [| discriminate].
  destruct (check_typed_structural_program
              (typed_certificate_hooks base_hooks)
              decoded_program
              (typed_certificate_types certificate)
              (typed_certificate_root_arrow certificate))
    eqn:Htyped; [| discriminate].
  inversion Hcheck; subst decoded_program.
  split; assumption.
Qed.

Theorem check_compiled_multisig_typed_byte_certificate_streaming_evidence :
  forall alg base_hooks certificate program,
    check_compiled_multisig_typed_byte_certificate_streaming
      alg base_hooks certificate = Some program ->
    TypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg
      (typed_certificate_hooks base_hooks)
      (typed_certificate_bytes certificate)
      program
      (typed_certificate_types certificate)
      (typed_certificate_root_arrow certificate).
Proof.
  intros alg base_hooks certificate program Hcheck.
  apply check_compiled_multisig_typed_byte_certificate_streaming_sound
    in Hcheck as [Hbytes Htyped].
  apply check_compiled_multisig_byte_certificate_streaming_typed_bridge_evidence;
    assumption.
Qed.

Theorem check_compiled_multisig_typed_byte_certificate_streaming_without_cmr_evidence :
  forall base_hooks certificate program,
    check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
      base_hooks certificate = Some program ->
    TypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      (typed_certificate_hooks base_hooks)
      (typed_certificate_bytes certificate)
      program
      (typed_certificate_types certificate)
      (typed_certificate_root_arrow certificate).
Proof.
  intros base_hooks certificate program Hcheck.
  apply check_compiled_multisig_typed_byte_certificate_streaming_without_cmr_sound
    in Hcheck as [Hbytes Htyped].
  apply check_compiled_multisig_byte_certificate_streaming_typed_decode_evidence;
    assumption.
Qed.

Definition check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
    (base_hooks : TypeHooks)
    (certificate : CompactCompiledMultisigTypedByteCertificate) :
    option StructuralProgram :=
  match expand_compact_typed_certificate certificate with
  | Some typed_certificate =>
      check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
        base_hooks
        typed_certificate
  | None => None
  end.

Definition check_compiled_multisig_compact_typed_byte_certificate_streaming
    (alg : CmrAlgebra)
    (base_hooks : TypeHooks)
    (certificate : CompactCompiledMultisigTypedByteCertificate) :
    option StructuralProgram :=
  match expand_compact_typed_certificate certificate with
  | Some typed_certificate =>
      check_compiled_multisig_typed_byte_certificate_streaming
        alg
        base_hooks
        typed_certificate
  | None => None
  end.

Record CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
    (base_hooks : TypeHooks)
    (certificate : CompactCompiledMultisigTypedByteCertificate)
    (program : StructuralProgram) : Prop := {
  compact_typed_decode_evidence :
    exists typed_certificate,
      expand_compact_typed_certificate certificate = Some typed_certificate /\
      TypedCompiledMultisigByteCertificateStreamingDecodeEvidence
        (typed_certificate_hooks base_hooks)
        (typed_certificate_bytes typed_certificate)
        program
        (typed_certificate_types typed_certificate)
        (typed_certificate_root_arrow typed_certificate)
}.

Record CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
    (alg : CmrAlgebra)
    (base_hooks : TypeHooks)
    (certificate : CompactCompiledMultisigTypedByteCertificate)
    (program : StructuralProgram) : Prop := {
  compact_typed_bridge_evidence :
    exists typed_certificate,
      expand_compact_typed_certificate certificate = Some typed_certificate /\
      TypedCompiledMultisigByteCertificateStreamingBridgeEvidence
        alg
        (typed_certificate_hooks base_hooks)
        (typed_certificate_bytes typed_certificate)
        program
        (typed_certificate_types typed_certificate)
        (typed_certificate_root_arrow typed_certificate)
}.

Theorem check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr_evidence :
  forall base_hooks certificate program,
    check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
      base_hooks certificate = Some program ->
    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      base_hooks certificate program.
Proof.
  intros base_hooks certificate program Hcheck.
  unfold check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
    in Hcheck.
  destruct (expand_compact_typed_certificate certificate)
    as [typed_certificate |] eqn:Hexpand; [| discriminate].
  constructor.
  exists typed_certificate.
  split.
  - exact Hexpand.
  - exact
      (@check_compiled_multisig_typed_byte_certificate_streaming_without_cmr_evidence
        base_hooks
        typed_certificate
        program
        Hcheck).
Qed.

Theorem compact_typed_byte_certificate_streaming_decode_evidence_from_byte_evidence :
  forall base_hooks certificate typed_certificate program,
    expand_compact_typed_certificate certificate = Some typed_certificate ->
    CompiledMultisigByteCertificateStreamingDecodeEvidence
      (compact_typed_certificate_bytes certificate)
      program ->
    check_typed_structural_program
      (typed_certificate_hooks base_hooks)
      program
      (typed_certificate_types typed_certificate)
      (typed_certificate_root_arrow typed_certificate) = true ->
    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      base_hooks certificate program.
Proof.
  intros base_hooks certificate typed_certificate program
    Hexpand Hbytes Htyped.
  constructor.
  exists typed_certificate.
  split.
  - exact Hexpand.
  - pose proof Hexpand as Hexpanded.
    unfold expand_compact_typed_certificate in Hexpanded.
    destruct (decode_compact_bridge_type_defs
                (compact_bridge_type_defs certificate)) as [types |]
      eqn:Htypes; [| discriminate].
    destruct (decode_compact_bridge_arrow_defs
                types
                (compact_bridge_arrow_defs certificate)) as [arrows |]
      eqn:Harrows; [| discriminate].
    destruct (decode_compact_type_table_entries
                arrows
                (compact_type_table_entries certificate)) as [type_table |]
      eqn:Htype_table; [| discriminate].
    destruct (nth_error arrows (compact_root_arrow_index certificate))
      as [root_arrow |] eqn:Hroot; [| discriminate].
    inversion Hexpanded; subst typed_certificate; simpl in *.
    apply compiled_multisig_byte_certificate_streaming_decode_evidence_typed.
    + exact Hbytes.
    + exact Htyped.
Qed.

Theorem compact_typed_byte_certificate_streaming_bridge_evidence_from_decode_and_cmr :
  forall alg base_hooks certificate program,
    CmrAlgebraWellFormed alg ->
    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      base_hooks certificate program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits (compact_typed_certificate_bytes certificate)) ->
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg base_hooks certificate program.
Proof.
  intros alg base_hooks certificate program Halg Hdecode Hcmr.
  destruct Hdecode as [[typed_certificate [Hexpand Htyped_decode]]].
  constructor.
  exists typed_certificate.
  split.
  - exact Hexpand.
  - pose proof Hexpand as Hexpanded.
    unfold expand_compact_typed_certificate in Hexpanded.
    destruct (decode_compact_bridge_type_defs
                (compact_bridge_type_defs certificate)) as [types |]
      eqn:Htypes; [| discriminate].
    destruct (decode_compact_bridge_arrow_defs
                types
                (compact_bridge_arrow_defs certificate)) as [arrows |]
      eqn:Harrows; [| discriminate].
    destruct (decode_compact_type_table_entries
                arrows
                (compact_type_table_entries certificate)) as [type_table |]
      eqn:Htype_table; [| discriminate].
    destruct (nth_error arrows (compact_root_arrow_index certificate))
      as [root_arrow |] eqn:Hroot; [| discriminate].
    inversion Hexpanded; subst typed_certificate; simpl in *.
    eapply typed_compiled_multisig_byte_certificate_streaming_bridge_evidence_from_decode_and_cmr.
    + exact Halg.
    + exact Htyped_decode.
    + exact Hcmr.
Qed.

Theorem check_compiled_multisig_compact_typed_byte_certificate_streaming_evidence :
  forall alg base_hooks certificate program,
    check_compiled_multisig_compact_typed_byte_certificate_streaming
      alg base_hooks certificate = Some program ->
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg base_hooks certificate program.
Proof.
  intros alg base_hooks certificate program Hcheck.
  unfold check_compiled_multisig_compact_typed_byte_certificate_streaming
    in Hcheck.
  destruct (expand_compact_typed_certificate certificate)
    as [typed_certificate |] eqn:Hexpand; [| discriminate].
  constructor.
  exists typed_certificate.
  split.
  - exact Hexpand.
  - exact
      (@check_compiled_multisig_typed_byte_certificate_streaming_evidence
        alg
        base_hooks
        typed_certificate
        program
        Hcheck).
Qed.

Theorem compact_typed_byte_certificate_streaming_bridge_byte_evidence :
  forall alg base_hooks certificate program,
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg base_hooks certificate program ->
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg (compact_typed_certificate_bytes certificate) program.
Proof.
  intros alg base_hooks certificate program Hbridge.
  destruct Hbridge as [[typed_certificate [Hexpand Htyped_bridge]]].
  destruct Htyped_bridge as [Hbyte _].
  unfold expand_compact_typed_certificate in Hexpand.
  destruct (decode_compact_bridge_type_defs
              (compact_bridge_type_defs certificate)) as [types |]
    eqn:Htypes; [| discriminate].
  destruct (decode_compact_bridge_arrow_defs
              types
              (compact_bridge_arrow_defs certificate)) as [arrows |]
    eqn:Harrows; [| discriminate].
  destruct (decode_compact_type_table_entries
              arrows
              (compact_type_table_entries certificate)) as [type_table |]
    eqn:Htype_table; [| discriminate].
  destruct (nth_error arrows (compact_root_arrow_index certificate))
    as [root_arrow |] eqn:Hroot; [| discriminate].
  inversion Hexpand; subst typed_certificate; simpl in Hbyte.
  exact Hbyte.
Qed.

Theorem compact_typed_byte_certificate_streaming_bridge_decoded_program :
  forall alg base_hooks certificate program,
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg base_hooks certificate program ->
    decode_structural_program_bytes_streaming
      (cert_program_bytes (compact_typed_certificate_bytes certificate)) =
      Some program.
Proof.
  intros alg base_hooks certificate program Hbridge.
  pose proof
    (@compact_typed_byte_certificate_streaming_bridge_byte_evidence
      alg base_hooks certificate program Hbridge) as Hbyte.
  exact (streaming_bridge_decoded_program Hbyte).
Qed.

Theorem compact_typed_byte_certificate_streaming_bridge_checked_cmr :
  forall alg base_hooks certificate program,
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg base_hooks certificate program ->
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits (compact_typed_certificate_bytes certificate)).
Proof.
  intros alg base_hooks certificate program Hbridge.
  pose proof
    (@compact_typed_byte_certificate_streaming_bridge_byte_evidence
      alg base_hooks certificate program Hbridge) as Hbyte.
  exact (streaming_bridge_checked_cmr Hbyte).
Qed.
