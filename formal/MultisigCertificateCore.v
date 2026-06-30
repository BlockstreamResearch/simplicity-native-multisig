From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import
  CmrWellFormed SimplicityByteDecoder MultisigSecurity
  MultisigSourceBlocks TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Byte-level certificate format for one compiled multisig covenant instance.

  The Rust side exports this shape as JSON: threshold, three participant public
  keys, no-witness Simplicity program bytes, and the expected CMR bytes.  This
  module is the Coq-side checker boundary.  It validates the byte-shaped fields
  before invoking the executable Simplicity byte decoder and checked CMR
  verifier from SimplicityByteDecoder.v.
*)

Record CompiledMultisigByteCertificate := {
  cert_threshold : nat;
  cert_participants : list (list byte);
  cert_program_bytes : list byte;
  cert_cmr_bytes : list byte
}.

Definition byte_well_formed (b : byte) : bool :=
  b <=? 255.

Definition bytes_well_formed (bytes : list byte) : bool :=
  forallb byte_well_formed bytes.

Fixpoint bytes_eqb (lhs rhs : list byte) : bool :=
  match lhs, rhs with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && bytes_eqb xs ys
  | _, _ => false
  end.

Definition participant_bytes_well_formed (participant : list byte) : bool :=
  Nat.eqb (length participant) 32 && bytes_well_formed participant.

Definition participants_distinct_well_formed
    (participants : list (list byte)) : bool :=
  match participants with
  | [participant1; participant2; participant3] =>
      negb (bytes_eqb participant1 participant2) &&
      negb (bytes_eqb participant1 participant3) &&
      negb (bytes_eqb participant2 participant3)
  | _ => false
  end.

Definition participants_well_formed (participants : list (list byte)) : bool :=
  Nat.eqb (length participants) 3 &&
  forallb participant_bytes_well_formed participants &&
  participants_distinct_well_formed participants.

Definition threshold_well_formed (threshold : nat) : bool :=
  (1 <=? threshold) && (threshold <=? 3).

Definition certificate_shape_well_formed
    (certificate : CompiledMultisigByteCertificate) : bool :=
  threshold_well_formed (cert_threshold certificate) &&
  participants_well_formed (cert_participants certificate) &&
  bytes_well_formed (cert_program_bytes certificate) &&
  Nat.eqb (length (cert_cmr_bytes certificate)) 32 &&
  bytes_well_formed (cert_cmr_bytes certificate).

Definition certificate_static_fields_well_formed
    (certificate : CompiledMultisigByteCertificate) : Prop :=
  1 <= cert_threshold certificate /\
  cert_threshold certificate <= participant_count /\
  length (cert_participants certificate) = participant_count /\
  NoDup (cert_participants certificate) /\
  Forall
    (fun participant =>
      length participant = 32 /\ bytes_well_formed participant = true)
    (cert_participants certificate) /\
  bytes_well_formed (cert_program_bytes certificate) = true /\
  length (cert_cmr_bytes certificate) = 32 /\
  bytes_well_formed (cert_cmr_bytes certificate) = true.

Definition certificate_cmr_bits
    (certificate : CompiledMultisigByteCertificate) : CmrBits :=
  bytes_to_bits (cert_cmr_bytes certificate).

Lemma bits_of_byte_length :
  forall b,
    length (bits_of_byte b) = 8.
Proof.
  intros b.
  unfold bits_of_byte.
  simpl.
  reflexivity.
Qed.

Lemma bytes_to_bits_length :
  forall bytes,
    length (bytes_to_bits bytes) = 8 * length bytes.
Proof.
  induction bytes as [| byte rest IH].
  - reflexivity.
  - unfold bytes_to_bits in *.
    simpl.
    rewrite IH.
    lia.
Qed.

Lemma certificate_cmr_bits_length_from_static_fields :
  forall certificate,
    certificate_static_fields_well_formed certificate ->
    length (certificate_cmr_bits certificate) = 256.
Proof.
  intros certificate Hstatic.
  destruct Hstatic as
    (_ & _ & _ & _ & _ & _ & Hcmr_length & _).
  unfold certificate_cmr_bits.
  rewrite bytes_to_bits_length.
  rewrite Hcmr_length.
  lia.
Qed.

Definition check_compiled_multisig_byte_certificate
    (alg : CmrAlgebra)
    (certificate : CompiledMultisigByteCertificate) :
    option StructuralProgram :=
  if certificate_shape_well_formed certificate then
    decode_structural_program_bytes_with_checked_cmr
      alg
      (cert_program_bytes certificate)
      (certificate_cmr_bits certificate)
  else None.

Definition check_compiled_multisig_byte_certificate_streaming
    (alg : CmrAlgebra)
    (certificate : CompiledMultisigByteCertificate) :
    option StructuralProgram :=
  if certificate_shape_well_formed certificate then
    decode_structural_program_bytes_streaming_with_checked_cmr
      alg
      (cert_program_bytes certificate)
      (certificate_cmr_bits certificate)
  else None.

Definition check_compiled_multisig_byte_certificate_without_cmr
    (certificate : CompiledMultisigByteCertificate) :
    option StructuralProgram :=
  if certificate_shape_well_formed certificate then
    decode_structural_program_bytes (cert_program_bytes certificate)
  else None.

Definition check_compiled_multisig_byte_certificate_streaming_without_cmr
    (certificate : CompiledMultisigByteCertificate) :
    option StructuralProgram :=
  if certificate_shape_well_formed certificate then
    decode_structural_program_bytes_streaming (cert_program_bytes certificate)
  else None.

Record CompiledMultisigByteCertificateDecodeEvidence
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram) : Prop := {
  decode_static_fields :
    certificate_static_fields_well_formed certificate;
  decode_decoded_program :
    decode_structural_program_bytes (cert_program_bytes certificate) =
      Some program;
  decode_raw_program :
    exists raw,
      decode_program_bytes (cert_program_bytes certificate) = Some raw /\
      validate_raw_program raw = Some program /\
      raw_canonical_order raw = true /\
      raw_program_children_before_from 0 raw;
  decode_hidden_cmrs_unique :
    structural_program_hidden_cmrs_unique program;
  decode_hidden_cmrs_256 :
    structural_program_hidden_cmrs_256 program;
  decode_multisig_jet_subset :
    structural_program_uses_only_multisig_jets program;
  decode_dag_well_formed :
    structural_program_dag_well_formed program = true;
  decode_dag_len_bound :
    length (structural_nodes program) <= dag_len_max;
  decode_child_references :
    structural_program_child_references_are_backward_nodes program;
  decode_no_fail :
    structural_program_no_fail program = true;
  decode_no_disconnect1 :
    structural_program_no_disconnect1 program = true;
  decode_closed_padding :
    program_bytes_closed_padding (cert_program_bytes certificate) = true
}.

Record CompiledMultisigByteCertificateStreamingDecodeEvidence
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram) : Prop := {
  streaming_decode_static_fields :
    certificate_static_fields_well_formed certificate;
  streaming_decode_decoded_program :
    decode_structural_program_bytes_streaming
      (cert_program_bytes certificate) =
      Some program;
  streaming_decode_raw_program :
    exists raw,
      decode_program_bytes_streaming (cert_program_bytes certificate) =
        Some raw /\
      validate_raw_program raw = Some program /\
      raw_canonical_order raw = true /\
      raw_program_children_before_from 0 raw;
  streaming_decode_hidden_cmrs_unique :
    structural_program_hidden_cmrs_unique program;
  streaming_decode_hidden_cmrs_256 :
    structural_program_hidden_cmrs_256 program;
  streaming_decode_multisig_jet_subset :
    structural_program_uses_only_multisig_jets program;
  streaming_decode_dag_well_formed :
    structural_program_dag_well_formed program = true;
  streaming_decode_dag_len_bound :
    length (structural_nodes program) <= dag_len_max;
  streaming_decode_child_references :
    structural_program_child_references_are_backward_nodes program;
  streaming_decode_no_fail :
    structural_program_no_fail program = true;
  streaming_decode_no_disconnect1 :
    structural_program_no_disconnect1 program = true;
  streaming_decode_closed_padding :
    program_bytes_streaming_closed_padding
      (cert_program_bytes certificate) = true
}.

Record CompiledMultisigByteCertificateStreamingBridgeEvidence
    (alg : CmrAlgebra)
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram) : Prop := {
  streaming_bridge_static_fields :
    certificate_static_fields_well_formed certificate;
  streaming_bridge_decoded_program :
    decode_structural_program_bytes_streaming
      (cert_program_bytes certificate) =
      Some program;
  streaming_bridge_raw_program :
    exists raw,
      decode_program_bytes_streaming (cert_program_bytes certificate) =
        Some raw /\
      validate_raw_program raw = Some program /\
      raw_canonical_order raw = true /\
      raw_program_children_before_from 0 raw;
  streaming_bridge_hidden_cmrs_unique :
    structural_program_hidden_cmrs_unique program;
  streaming_bridge_hidden_cmrs_256 :
    structural_program_hidden_cmrs_256 program;
  streaming_bridge_checked_cmr :
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits certificate);
  streaming_bridge_cmr_bits_length :
    length (certificate_cmr_bits certificate) = 256;
  streaming_bridge_multisig_jet_subset :
    structural_program_uses_only_multisig_jets program;
  streaming_bridge_dag_well_formed :
    structural_program_dag_well_formed program = true;
  streaming_bridge_dag_len_bound :
    length (structural_nodes program) <= dag_len_max;
  streaming_bridge_child_references :
    structural_program_child_references_are_backward_nodes program;
  streaming_bridge_no_fail :
    structural_program_no_fail program = true;
  streaming_bridge_no_disconnect1 :
    structural_program_no_disconnect1 program = true;
  streaming_bridge_closed_padding :
    program_bytes_streaming_closed_padding
      (cert_program_bytes certificate) = true
}.

Record CompiledMultisigByteCertificateBridgeEvidence
    (alg : CmrAlgebra)
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram) : Prop := {
  bridge_static_fields :
    certificate_static_fields_well_formed certificate;
  bridge_decoded_program :
    decode_structural_program_bytes (cert_program_bytes certificate) =
      Some program;
  bridge_raw_program :
    exists raw,
      decode_program_bytes (cert_program_bytes certificate) = Some raw /\
      validate_raw_program raw = Some program /\
      raw_canonical_order raw = true /\
      raw_program_children_before_from 0 raw;
  bridge_hidden_cmrs_unique :
    structural_program_hidden_cmrs_unique program;
  bridge_hidden_cmrs_256 :
    structural_program_hidden_cmrs_256 program;
  bridge_checked_cmr :
    compute_structural_program_cmr_checked alg program =
      Some (certificate_cmr_bits certificate);
  bridge_cmr_bits_length :
    length (certificate_cmr_bits certificate) = 256;
  bridge_multisig_jet_subset :
    structural_program_uses_only_multisig_jets program;
  bridge_dag_well_formed :
    structural_program_dag_well_formed program = true;
  bridge_dag_len_bound :
    length (structural_nodes program) <= dag_len_max;
  bridge_child_references :
    structural_program_child_references_are_backward_nodes program;
  bridge_no_fail :
    structural_program_no_fail program = true;
  bridge_no_disconnect1 :
    structural_program_no_disconnect1 program = true;
  bridge_closed_padding :
    program_bytes_closed_padding (cert_program_bytes certificate) = true
}.

Record TypedCompiledMultisigByteCertificateBridgeEvidence
    (alg : CmrAlgebra)
    (hooks : TypeHooks)
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : Prop := {
  typed_compiled_byte_evidence :
    CompiledMultisigByteCertificateBridgeEvidence alg certificate program;
  typed_compiled_type_evidence :
    TypedByteBridgeEvidence hooks program types root_arrow
}.

Record TypedCompiledMultisigByteCertificateStreamingBridgeEvidence
    (alg : CmrAlgebra)
    (hooks : TypeHooks)
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : Prop := {
  typed_compiled_streaming_byte_evidence :
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg certificate program;
  typed_compiled_streaming_type_evidence :
    TypedByteBridgeEvidence hooks program types root_arrow
}.

Record TypedCompiledMultisigByteCertificateStreamingDecodeEvidence
    (hooks : TypeHooks)
    (certificate : CompiledMultisigByteCertificate)
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : Prop := {
  typed_compiled_streaming_decode_byte_evidence :
    CompiledMultisigByteCertificateStreamingDecodeEvidence certificate program;
  typed_compiled_streaming_decode_type_evidence :
    TypedByteBridgeEvidence hooks program types root_arrow
}.

Theorem compiled_multisig_byte_certificate_bridge_evidence_from_decode_and_cmr :
  forall alg certificate program,
    CmrAlgebraWellFormed alg ->
    CompiledMultisigByteCertificateDecodeEvidence certificate program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits certificate) ->
    CompiledMultisigByteCertificateBridgeEvidence alg certificate program.
Proof.
  intros alg certificate program Halg Hdecode Hcmr.
  destruct Hdecode as
    [Hstatic Hdecoded Hraw Hhidden_unique Hhidden_256 Hjets Hdag Hdag_bound
     Hchildren Hno_fail Hno_disconnect1 Hpadding].
  constructor.
  - exact Hstatic.
  - exact Hdecoded.
  - exact Hraw.
  - exact Hhidden_unique.
  - exact Hhidden_256.
  - eapply compute_structural_program_cmr_checked_matches_unchecked.
    + exact Halg.
    + exact Hhidden_256.
    + exact Hcmr.
  - apply certificate_cmr_bits_length_from_static_fields.
    exact Hstatic.
  - exact Hjets.
  - exact Hdag.
  - exact Hdag_bound.
  - exact Hchildren.
  - exact Hno_fail.
  - exact Hno_disconnect1.
  - exact Hpadding.
Qed.

Theorem compiled_multisig_byte_certificate_streaming_bridge_evidence_from_decode_and_cmr :
  forall alg certificate program,
    CmrAlgebraWellFormed alg ->
    CompiledMultisigByteCertificateStreamingDecodeEvidence
      certificate program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits certificate) ->
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg certificate program.
Proof.
  intros alg certificate program Halg Hdecode Hcmr.
  destruct Hdecode as
    [Hstatic Hdecoded Hraw Hhidden_unique Hhidden_256 Hjets Hdag Hdag_bound
     Hchildren Hno_fail Hno_disconnect1 Hpadding].
  constructor.
  - exact Hstatic.
  - exact Hdecoded.
  - exact Hraw.
  - exact Hhidden_unique.
  - exact Hhidden_256.
  - eapply compute_structural_program_cmr_checked_matches_unchecked.
    + exact Halg.
    + exact Hhidden_256.
    + exact Hcmr.
  - apply certificate_cmr_bits_length_from_static_fields.
    exact Hstatic.
  - exact Hjets.
  - exact Hdag.
  - exact Hdag_bound.
  - exact Hchildren.
  - exact Hno_fail.
  - exact Hno_disconnect1.
  - exact Hpadding.
Qed.

Theorem typed_compiled_multisig_byte_certificate_streaming_bridge_evidence_from_decode_and_cmr :
  forall alg hooks certificate program types root_arrow,
    CmrAlgebraWellFormed alg ->
    TypedCompiledMultisigByteCertificateStreamingDecodeEvidence
      hooks certificate program types root_arrow ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits certificate) ->
    TypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg hooks certificate program types root_arrow.
Proof.
  intros alg hooks certificate program types root_arrow Halg Hdecode Hcmr.
  destruct Hdecode as [Hbyte Htyped].
  constructor.
  - eapply compiled_multisig_byte_certificate_streaming_bridge_evidence_from_decode_and_cmr.
    + exact Halg.
    + exact Hbyte.
    + exact Hcmr.
  - exact Htyped.
Qed.

