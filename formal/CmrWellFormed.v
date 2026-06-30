From Coq Require Import List Arith.
From MultisigFormal Require Import
  ElementsJetCmr SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Well-formedness layer for CMR algebras.

  The byte decoder can run with any executable CmrAlgebra, so the checked CMR
  path verifies that every intermediate/root CMR has 256 bits.  The real
  foundation-backed algebra should satisfy this contract by construction.  The
  lemmas below let later proofs discharge the checked path from an ordinary CMR
  computation plus this well-formedness proof, without changing the decoder.
*)

Definition zero_hash256_bits_length :
  cmr_bits_length_256 zero_hash256_bits.
Proof.
  unfold cmr_bits_length_256, zero_hash256_bits.
  rewrite repeat_length.
  reflexivity.
Qed.

Record CmrAlgebraWellFormed (alg : CmrAlgebra) : Prop := {
  cmr_iden_well_formed :
    cmr_bits_length_256 (cmr_iden alg);
  cmr_unit_well_formed :
    cmr_bits_length_256 (cmr_unit alg);
  cmr_injl_well_formed :
    forall child, cmr_bits_length_256 (cmr_injl alg child);
  cmr_injr_well_formed :
    forall child, cmr_bits_length_256 (cmr_injr alg child);
  cmr_take_well_formed :
    forall child, cmr_bits_length_256 (cmr_take alg child);
  cmr_drop_well_formed :
    forall child, cmr_bits_length_256 (cmr_drop alg child);
  cmr_comp_well_formed :
    forall lhs rhs, cmr_bits_length_256 (cmr_comp alg lhs rhs);
  cmr_case_well_formed :
    forall lhs rhs, cmr_bits_length_256 (cmr_case alg lhs rhs);
  cmr_pair_well_formed :
    forall lhs rhs, cmr_bits_length_256 (cmr_pair alg lhs rhs);
  cmr_disconnect_well_formed :
    forall child, cmr_bits_length_256 (cmr_disconnect alg child);
  cmr_witness_well_formed :
    cmr_bits_length_256 (cmr_witness alg);
  cmr_fail_well_formed :
    forall entropy_bits, cmr_bits_length_256 (cmr_fail alg entropy_bits);
  cmr_jet_well_formed :
    forall jet, cmr_bits_length_256 (cmr_jet alg jet);
  cmr_word_well_formed :
    forall encoded_width value_bits,
      cmr_bits_length_256 (cmr_word alg encoded_width value_bits)
}.

Lemma require_cmr_bits_length_256 :
  forall cmr_bits,
    cmr_bits_length_256 cmr_bits ->
    require_cmr_bits cmr_bits = Some cmr_bits.
Proof.
  intros cmr_bits Hlength.
  unfold require_cmr_bits, cmr_bits_well_formed.
  unfold cmr_bits_length_256 in Hlength.
  rewrite Hlength.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma compute_structural_node_cmr_well_formed :
  forall alg computed node node_cmr,
    CmrAlgebraWellFormed alg ->
    compute_structural_node_cmr alg computed node = Some node_cmr ->
    cmr_bits_length_256 node_cmr.
Proof.
  intros alg computed node node_cmr Halg Hcompute.
  destruct Halg as
    [Hiden Hunit Hinjl Hinjr Htake Hdrop Hcomp Hcase Hpair
     Hdisconnect Hwitness Hfail Hjet Hword].
  destruct node; simpl in Hcompute.
  - inversion Hcompute; subst. exact Hiden.
  - inversion Hcompute; subst. exact Hunit.
  - destruct (nth_error computed child); [| discriminate].
    inversion Hcompute; subst. apply Hinjl.
  - destruct (nth_error computed child); [| discriminate].
    inversion Hcompute; subst. apply Hinjr.
  - destruct (nth_error computed child); [| discriminate].
    inversion Hcompute; subst. apply Htake.
  - destruct (nth_error computed child); [| discriminate].
    inversion Hcompute; subst. apply Hdrop.
  - destruct (nth_error computed lhs); [| discriminate].
    destruct (nth_error computed rhs); [| discriminate].
    inversion Hcompute; subst. apply Hcomp.
  - destruct (nth_error computed lhs); [| discriminate].
    destruct (nth_error computed rhs); [| discriminate].
    inversion Hcompute; subst. apply Hcase.
  - destruct (nth_error computed lhs); [| discriminate].
    inversion Hcompute; subst. apply Hcase.
  - destruct (nth_error computed rhs); [| discriminate].
    inversion Hcompute; subst. apply Hcase.
  - destruct (nth_error computed lhs); [| discriminate].
    destruct (nth_error computed rhs); [| discriminate].
    inversion Hcompute; subst. apply Hpair.
  - destruct (nth_error computed lhs); [| discriminate].
    inversion Hcompute; subst. apply Hdisconnect.
  - destruct (nth_error computed lhs); [| discriminate].
    destruct (nth_error computed rhs); [| discriminate].
    inversion Hcompute; subst. apply Hdisconnect.
  - inversion Hcompute; subst. exact Hwitness.
  - inversion Hcompute; subst. apply Hfail.
  - inversion Hcompute; subst. apply Hjet.
  - inversion Hcompute; subst. apply Hword.
Qed.

Lemma compute_converted_node_cmr_well_formed :
  forall alg computed node node_cmr,
    CmrAlgebraWellFormed alg ->
    Forall cmr_bits_length_256 (converted_node_hidden_cmrs node) ->
    compute_converted_node_cmr alg computed node = Some node_cmr ->
    cmr_bits_length_256 node_cmr.
Proof.
  intros alg computed node node_cmr Halg Hhidden Hcompute.
  destruct node as [structural | hidden_cmr]; simpl in Hcompute.
  - eapply compute_structural_node_cmr_well_formed; eauto.
  - inversion Hcompute; subst.
    inversion Hhidden as [| ? ? Hhead ?]; subst.
    exact Hhead.
Qed.

Lemma compute_cmr_nodes_preserves_well_formed :
  forall alg nodes computed computed',
    CmrAlgebraWellFormed alg ->
    Forall cmr_bits_length_256 (converted_nodes_hidden_cmrs nodes) ->
    Forall cmr_bits_length_256 computed ->
    compute_cmr_nodes alg nodes computed = Some computed' ->
    Forall cmr_bits_length_256 computed'.
Proof.
  intros alg nodes.
  induction nodes as [| node rest IH];
    intros computed computed' Halg Hhidden Hcomputed Hcompute;
    simpl in Hcompute.
  - inversion Hcompute; subst. exact Hcomputed.
  - simpl in Hhidden.
    apply Forall_app in Hhidden as [Hnode_hidden Hrest_hidden].
    destruct (compute_converted_node_cmr alg computed node)
      as [node_cmr |] eqn:Hnode; [| discriminate].
    apply IH with (computed := computed ++ [node_cmr]).
    + exact Halg.
    + exact Hrest_hidden.
    + apply Forall_app. split.
      * exact Hcomputed.
      * constructor.
        -- eapply compute_converted_node_cmr_well_formed; eauto.
        -- constructor.
    + exact Hcompute.
Qed.

Lemma compute_cmr_nodes_checked_matches_unchecked :
  forall alg nodes computed computed',
    CmrAlgebraWellFormed alg ->
    Forall cmr_bits_length_256 (converted_nodes_hidden_cmrs nodes) ->
    Forall cmr_bits_length_256 computed ->
    compute_cmr_nodes alg nodes computed = Some computed' ->
    compute_cmr_nodes_checked alg nodes computed = Some computed'.
Proof.
  intros alg nodes.
  induction nodes as [| node rest IH];
    intros computed computed' Halg Hhidden Hcomputed Hcompute;
    simpl in Hcompute |- *.
  - exact Hcompute.
  - simpl in Hhidden.
    apply Forall_app in Hhidden as [Hnode_hidden Hrest_hidden].
    destruct (compute_converted_node_cmr alg computed node)
      as [node_cmr |] eqn:Hnode; [| discriminate].
    assert (Hnode_cmr : cmr_bits_length_256 node_cmr).
    {
      eapply compute_converted_node_cmr_well_formed; eauto.
    }
    rewrite (@require_cmr_bits_length_256 node_cmr Hnode_cmr).
    eapply IH.
    + exact Halg.
    + exact Hrest_hidden.
    + apply Forall_app. split.
      * exact Hcomputed.
      * constructor; [exact Hnode_cmr | constructor].
    + exact Hcompute.
Qed.

Theorem compute_structural_program_cmr_checked_matches_unchecked :
  forall alg program cmr,
    CmrAlgebraWellFormed alg ->
    structural_program_hidden_cmrs_256 program ->
    compute_structural_program_cmr alg program = Some cmr ->
    compute_structural_program_cmr_checked alg program = Some cmr.
Proof.
  intros alg program cmr Halg Hhidden Hcompute.
  unfold compute_structural_program_cmr in Hcompute.
  unfold compute_structural_program_cmr_checked.
  unfold structural_program_hidden_cmrs_256 in Hhidden.
  unfold structural_program_hidden_cmrs in Hhidden.
  destruct (compute_cmr_nodes alg (structural_nodes program) [])
    as [computed |] eqn:Hnodes; [| discriminate].
  assert (Hchecked :
    compute_cmr_nodes_checked alg (structural_nodes program) [] =
      Some computed).
  {
    eapply compute_cmr_nodes_checked_matches_unchecked.
    - exact Halg.
    - exact Hhidden.
    - constructor.
    - exact Hnodes.
  }
  change
    (match compute_cmr_nodes_checked alg (structural_nodes program) [] with
     | Some computed' => nth_error computed' (structural_root program)
     | None => None
     end = Some cmr).
  rewrite Hchecked.
  exact Hcompute.
Qed.

Theorem verify_structural_program_cmr_checked_if_unchecked :
  forall alg program expected_cmr,
    CmrAlgebraWellFormed alg ->
    structural_program_hidden_cmrs_256 program ->
    cmr_bits_length_256 expected_cmr ->
    verify_structural_program_cmr alg program expected_cmr = true ->
    verify_structural_program_cmr_checked alg program expected_cmr = true.
Proof.
  intros alg program expected_cmr Halg Hhidden Hexpected Hverify.
  unfold verify_structural_program_cmr in Hverify.
  destruct (compute_structural_program_cmr alg program)
    as [actual_cmr |] eqn:Hcompute; [| discriminate].
  unfold verify_structural_program_cmr_checked.
  rewrite (@require_cmr_bits_length_256 expected_cmr Hexpected).
  rewrite (@compute_structural_program_cmr_checked_matches_unchecked
    alg program actual_cmr Halg Hhidden Hcompute).
  exact Hverify.
Qed.

Theorem decode_structural_program_bytes_with_checked_cmr_from_unchecked :
  forall alg bytes expected_cmr program,
    CmrAlgebraWellFormed alg ->
    cmr_bits_length_256 expected_cmr ->
    decode_structural_program_bytes_with_cmr alg bytes expected_cmr =
      Some program ->
    decode_structural_program_bytes_with_checked_cmr alg bytes expected_cmr =
      Some program.
Proof.
  intros alg bytes expected_cmr program Halg Hexpected Hdecode.
  unfold decode_structural_program_bytes_with_cmr in Hdecode.
  unfold decode_structural_program_bytes_with_checked_cmr.
  destruct (decode_structural_program_bytes bytes)
    as [decoded_program |] eqn:Hprogram; [| discriminate].
  destruct (verify_structural_program_cmr alg decoded_program expected_cmr)
    eqn:Hverify; [| discriminate].
  inversion Hdecode; subst decoded_program.
  assert (Hhidden : structural_program_hidden_cmrs_256 program).
  {
    eapply decode_structural_program_bytes_hidden_cmrs_256.
    exact Hprogram.
  }
  rewrite (@verify_structural_program_cmr_checked_if_unchecked
    alg program expected_cmr Halg Hhidden Hexpected Hverify).
  reflexivity.
Qed.

Theorem decode_structural_program_bytes_streaming_with_checked_cmr_from_unchecked :
  forall alg bytes expected_cmr program,
    CmrAlgebraWellFormed alg ->
    cmr_bits_length_256 expected_cmr ->
    decode_structural_program_bytes_streaming_with_cmr alg bytes expected_cmr =
      Some program ->
    decode_structural_program_bytes_streaming_with_checked_cmr
      alg bytes expected_cmr =
      Some program.
Proof.
  intros alg bytes expected_cmr program Halg Hexpected Hdecode.
  unfold decode_structural_program_bytes_streaming_with_cmr in Hdecode.
  unfold decode_structural_program_bytes_streaming_with_checked_cmr.
  destruct (decode_structural_program_bytes_streaming bytes)
    as [decoded_program |] eqn:Hprogram; [| discriminate].
  destruct (verify_structural_program_cmr alg decoded_program expected_cmr)
    eqn:Hverify; [| discriminate].
  inversion Hdecode; subst decoded_program.
  assert (Hhidden : structural_program_hidden_cmrs_256 program).
  {
    eapply decode_structural_program_bytes_streaming_hidden_cmrs_256.
    exact Hprogram.
  }
  rewrite (@verify_structural_program_cmr_checked_if_unchecked
    alg program expected_cmr Halg Hhidden Hexpected Hverify).
  reflexivity.
Qed.

Example zero_cmr_alg_well_formed :
  CmrAlgebraWellFormed zero_cmr_alg.
Proof.
  constructor; simpl; intros; apply zero_hash256_bits_length.
Qed.

Theorem with_elements_jet_cmr_well_formed :
  forall alg,
    CmrAlgebraWellFormed alg ->
    CmrAlgebraWellFormed (with_elements_jet_cmr alg).
Proof.
  intros alg Halg.
  destruct Halg as
    [Hiden Hunit Hinjl Hinjr Htake Hdrop Hcomp Hcase Hpair
     Hdisconnect Hwitness Hfail _ Hword].
  constructor; simpl.
  - exact Hiden.
  - exact Hunit.
  - exact Hinjl.
  - exact Hinjr.
  - exact Htake.
  - exact Hdrop.
  - exact Hcomp.
  - exact Hcase.
  - exact Hpair.
  - exact Hdisconnect.
  - exact Hwitness.
  - exact Hfail.
  - exact elements_jet_cmr_bits_length.
  - exact Hword.
Qed.
