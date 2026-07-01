From Coq Require Import List.
From MultisigFormal Require Import
  CmrWellFormed ElementsJetCmr SimplicityByteDecoder.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Foundation-shaped CMR adapter for the local byte decoder.

  Upstream Simplicity computes commitment Merkle roots in
  /Volumes/Somebody/Desktop/Simp/simplicity/Coq/Simplicity/MerkleRoot.v:

    iden/unit/witness are commitment tags,
    injl/injr/take/drop/disconnect are compress_half tag child,
    comp/case/pair are compress tag left right,
    assertl/assertr use the same case tag.

  This file does not instantiate SHA256 or the tag constants.  Instead it
  records exactly the executable operations the byte-level checker needs.  A
  later foundation-backed instantiation should fill these fields from
  Simplicity.Digest and Simplicity.MerkleRoot.
*)

Record FoundationCmrOps := {
  foundation_cmr_iden_tag : CmrBits;
  foundation_cmr_comp_tag : CmrBits;
  foundation_cmr_unit_tag : CmrBits;
  foundation_cmr_injl_tag : CmrBits;
  foundation_cmr_injr_tag : CmrBits;
  foundation_cmr_case_tag : CmrBits;
  foundation_cmr_pair_tag : CmrBits;
  foundation_cmr_take_tag : CmrBits;
  foundation_cmr_drop_tag : CmrBits;
  foundation_cmr_witness_tag : CmrBits;
  foundation_cmr_disconnect_tag : CmrBits;

  foundation_cmr_compress :
    CmrBits -> CmrBits -> CmrBits -> CmrBits;
  foundation_cmr_compress_half :
    CmrBits -> CmrBits -> CmrBits;

  foundation_cmr_word :
    nat -> list bool -> CmrBits;
  foundation_cmr_fail :
    list bool -> CmrBits;
  foundation_cmr_jet :
    ElementsJet -> CmrBits;

  foundation_cmr_iden_tag_256 :
    cmr_bits_length_256 foundation_cmr_iden_tag;
  foundation_cmr_unit_tag_256 :
    cmr_bits_length_256 foundation_cmr_unit_tag;
  foundation_cmr_witness_tag_256 :
    cmr_bits_length_256 foundation_cmr_witness_tag;
  foundation_cmr_compress_256 :
    forall tag lhs rhs,
      cmr_bits_length_256
        (foundation_cmr_compress tag lhs rhs);
  foundation_cmr_compress_half_256 :
    forall tag child,
      cmr_bits_length_256
        (foundation_cmr_compress_half tag child);
  foundation_cmr_word_256 :
    forall encoded_width value_bits,
      cmr_bits_length_256
        (foundation_cmr_word encoded_width value_bits);
  foundation_cmr_fail_256 :
    forall entropy_bits,
      cmr_bits_length_256
        (foundation_cmr_fail entropy_bits);
  foundation_cmr_jet_256 :
    forall jet,
      cmr_bits_length_256
        (foundation_cmr_jet jet)
}.

Definition foundation_core_cmr_algebra
    (ops : FoundationCmrOps) : CmrAlgebra := {|
  cmr_iden := foundation_cmr_iden_tag ops;
  cmr_unit := foundation_cmr_unit_tag ops;
  cmr_injl :=
    foundation_cmr_compress_half ops
      (foundation_cmr_injl_tag ops);
  cmr_injr :=
    foundation_cmr_compress_half ops
      (foundation_cmr_injr_tag ops);
  cmr_take :=
    foundation_cmr_compress_half ops
      (foundation_cmr_take_tag ops);
  cmr_drop :=
    foundation_cmr_compress_half ops
      (foundation_cmr_drop_tag ops);
  cmr_comp :=
    foundation_cmr_compress ops
      (foundation_cmr_comp_tag ops);
  cmr_case :=
    foundation_cmr_compress ops
      (foundation_cmr_case_tag ops);
  cmr_pair :=
    foundation_cmr_compress ops
      (foundation_cmr_pair_tag ops);
  cmr_disconnect :=
    foundation_cmr_compress_half ops
      (foundation_cmr_disconnect_tag ops);
  cmr_witness := foundation_cmr_witness_tag ops;
  cmr_fail := foundation_cmr_fail ops;
  cmr_jet := foundation_cmr_jet ops;
  cmr_word := foundation_cmr_word ops
|}.

Definition foundation_elements_cmr_algebra
    (ops : FoundationCmrOps) : CmrAlgebra :=
  with_elements_jet_cmr (foundation_core_cmr_algebra ops).

Theorem foundation_core_cmr_algebra_compute_assertl :
  forall ops computed lhs lhs_cmr hidden_cmr,
    nth_error computed lhs = Some lhs_cmr ->
    compute_structural_node_cmr
      (foundation_core_cmr_algebra ops)
      computed
      (SAssertL lhs hidden_cmr) =
      Some
        (foundation_cmr_compress ops
          (foundation_cmr_case_tag ops)
          lhs_cmr
          hidden_cmr).
Proof.
  intros ops computed lhs lhs_cmr hidden_cmr Hlhs.
  simpl. rewrite Hlhs. reflexivity.
Qed.

Theorem foundation_core_cmr_algebra_compute_assertr :
  forall ops computed hidden_cmr rhs rhs_cmr,
    nth_error computed rhs = Some rhs_cmr ->
    compute_structural_node_cmr
      (foundation_core_cmr_algebra ops)
      computed
      (SAssertR hidden_cmr rhs) =
      Some
        (foundation_cmr_compress ops
          (foundation_cmr_case_tag ops)
          hidden_cmr
          rhs_cmr).
Proof.
  intros ops computed hidden_cmr rhs rhs_cmr Hrhs.
  simpl. rewrite Hrhs. reflexivity.
Qed.

Theorem foundation_core_cmr_algebra_compute_disconnect :
  forall ops computed lhs rhs lhs_cmr rhs_cmr,
    nth_error computed lhs = Some lhs_cmr ->
    nth_error computed rhs = Some rhs_cmr ->
    compute_structural_node_cmr
      (foundation_core_cmr_algebra ops)
      computed
      (SDisconnect lhs rhs) =
      Some
        (foundation_cmr_compress_half ops
          (foundation_cmr_disconnect_tag ops)
          lhs_cmr).
Proof.
  intros ops computed lhs rhs lhs_cmr rhs_cmr Hlhs Hrhs.
  simpl. rewrite Hlhs, Hrhs. reflexivity.
Qed.

Theorem foundation_elements_cmr_algebra_uses_elements_jet_cmr :
  forall ops jet,
    cmr_jet (foundation_elements_cmr_algebra ops) jet =
    elements_jet_cmr_bits jet.
Proof.
  intros ops jet.
  reflexivity.
Qed.

Theorem foundation_core_cmr_algebra_well_formed :
  forall ops,
    CmrAlgebraWellFormed (foundation_core_cmr_algebra ops).
Proof.
  intros ops.
  constructor; simpl.
  - apply foundation_cmr_iden_tag_256.
  - apply foundation_cmr_unit_tag_256.
  - intros. apply foundation_cmr_compress_half_256.
  - intros. apply foundation_cmr_compress_half_256.
  - intros. apply foundation_cmr_compress_half_256.
  - intros. apply foundation_cmr_compress_half_256.
  - intros. apply foundation_cmr_compress_256.
  - intros. apply foundation_cmr_compress_256.
  - intros. apply foundation_cmr_compress_256.
  - intros. apply foundation_cmr_compress_half_256.
  - apply foundation_cmr_witness_tag_256.
  - apply foundation_cmr_fail_256.
  - apply foundation_cmr_jet_256.
  - apply foundation_cmr_word_256.
Qed.

Theorem foundation_elements_cmr_algebra_well_formed :
  forall ops,
    CmrAlgebraWellFormed (foundation_elements_cmr_algebra ops).
Proof.
  intros ops.
  unfold foundation_elements_cmr_algebra.
  apply with_elements_jet_cmr_well_formed.
  apply foundation_core_cmr_algebra_well_formed.
Qed.
