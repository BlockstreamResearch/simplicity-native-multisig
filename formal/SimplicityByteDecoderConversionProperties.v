From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderConversionCore.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma convert_raw_node_backrefs_are_nodes :
  forall raw converted seen_hidden converted_node seen_hidden',
    convert_raw_node converted seen_hidden raw =
      Some (converted_node, seen_hidden') ->
    converted_node_backrefs_are_nodesb converted converted_node = true.
Proof.
  intros raw converted seen_hidden converted_node seen_hidden' Hconvert.
  destruct raw; simpl in Hconvert;
    try (inversion Hconvert; subst; reflexivity).
  - destruct (get_converted_node converted child) as [child_node |]
      eqn:Hchild; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hchild).
    reflexivity.
  - destruct (get_converted_node converted child) as [child_node |]
      eqn:Hchild; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hchild).
    reflexivity.
  - destruct (get_converted_node converted child) as [child_node |]
      eqn:Hchild; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hchild).
    reflexivity.
  - destruct (get_converted_node converted child) as [child_node |]
      eqn:Hchild; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hchild).
    reflexivity.
  - destruct (get_converted_node converted lhs) as [lhs_node |]
      eqn:Hlhs; [| discriminate].
    destruct (get_converted_node converted rhs) as [rhs_node |]
      eqn:Hrhs; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hlhs).
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hrhs).
    reflexivity.
  - destruct (nth_error converted lhs) as [[lhs_node | lhs_hidden] |]
      eqn:Hlhs;
    destruct (nth_error converted rhs) as [[rhs_node | rhs_hidden] |]
      eqn:Hrhs; try discriminate.
    + inversion Hconvert; subst.
      cbn [converted_node_backrefs_are_nodesb
        structural_node_backrefs_are_nodesb structural_node_children forallb].
      rewrite (@nth_error_cnode_child_is_nodeb _ _ _ Hlhs).
      rewrite (@nth_error_cnode_child_is_nodeb _ _ _ Hrhs).
      reflexivity.
    + inversion Hconvert; subst.
      cbn [converted_node_backrefs_are_nodesb
        structural_node_backrefs_are_nodesb structural_node_children forallb].
      rewrite (@nth_error_cnode_child_is_nodeb _ _ _ Hlhs).
      reflexivity.
    + inversion Hconvert; subst.
      cbn [converted_node_backrefs_are_nodesb
        structural_node_backrefs_are_nodesb structural_node_children forallb].
      rewrite (@nth_error_cnode_child_is_nodeb _ _ _ Hrhs).
      reflexivity.
  - destruct (get_converted_node converted lhs) as [lhs_node |]
      eqn:Hlhs; [| discriminate].
    destruct (get_converted_node converted rhs) as [rhs_node |]
      eqn:Hrhs; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hlhs).
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hrhs).
    reflexivity.
  - destruct (get_converted_node converted lhs) as [lhs_node |]
      eqn:Hlhs; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hlhs).
    reflexivity.
  - destruct (get_converted_node converted lhs) as [lhs_node |]
      eqn:Hlhs; [| discriminate].
    destruct (get_converted_node converted rhs) as [rhs_node |]
      eqn:Hrhs; [| discriminate].
    inversion Hconvert; subst.
    cbn [converted_node_backrefs_are_nodesb
      structural_node_backrefs_are_nodesb structural_node_children forallb].
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hlhs).
    rewrite (@get_converted_node_child_is_nodeb _ _ _ Hrhs).
    reflexivity.
  - destruct (hidden_seen cmr_bits seen_hidden); inversion Hconvert; subst;
      reflexivity.
Qed.

Lemma convert_raw_node_preserves_no_fail :
  forall raw converted seen_hidden converted_node seen_hidden',
    raw_node_no_fail raw = true ->
    convert_raw_node converted seen_hidden raw =
      Some (converted_node, seen_hidden') ->
    converted_node_no_fail converted_node = true.
Proof.
  intros raw converted seen_hidden converted_node seen_hidden'
    Hraw_no_fail Hconvert.
  destruct raw; simpl in Hraw_no_fail; try discriminate;
    simpl in Hconvert;
    repeat match goal with
    | H : context[match ?x with _ => _ end] |- _ =>
        destruct x eqn:?
    end;
    try discriminate;
    inversion Hconvert; subst; reflexivity.
Qed.

Lemma convert_raw_node_preserves_no_disconnect1 :
  forall raw converted seen_hidden converted_node seen_hidden',
    raw_node_no_disconnect1 raw = true ->
    convert_raw_node converted seen_hidden raw =
      Some (converted_node, seen_hidden') ->
    converted_node_no_disconnect1 converted_node = true.
Proof.
  intros raw converted seen_hidden converted_node seen_hidden'
    Hraw_no_disconnect1 Hconvert.
  destruct raw; simpl in Hraw_no_disconnect1; try discriminate;
    simpl in Hconvert;
    repeat match goal with
    | H : context[match ?x with _ => _ end] |- _ =>
        destruct x eqn:?
    end;
    try discriminate;
    inversion Hconvert; subst; reflexivity.
Qed.

Lemma convert_raw_node_hidden_seen_relation :
  forall raw converted seen_hidden converted_node seen_hidden',
    convert_raw_node converted seen_hidden raw =
      Some (converted_node, seen_hidden') ->
    converted_node_hidden_cmrs converted_node ++ seen_hidden = seen_hidden'.
Proof.
  intros raw converted seen_hidden converted_node seen_hidden' Hconvert.
  destruct raw; simpl in Hconvert;
    repeat match goal with
    | H : context[match ?x with _ => _ end] |- _ =>
        destruct x eqn:?
    end;
    try discriminate;
    inversion Hconvert; subst; reflexivity.
Qed.

Lemma convert_raw_node_preserves_seen_hidden_NoDup :
  forall raw converted seen_hidden converted_node seen_hidden',
    NoDup seen_hidden ->
    convert_raw_node converted seen_hidden raw =
      Some (converted_node, seen_hidden') ->
    NoDup seen_hidden'.
Proof.
  intros raw converted seen_hidden converted_node seen_hidden'
    Hnodup Hconvert.
  destruct raw; simpl in Hconvert;
    try
      (repeat match goal with
      | H : context[match ?x with _ => _ end] |- _ =>
          destruct x eqn:?
      end;
      try discriminate;
      inversion Hconvert; subst; exact Hnodup).
  destruct (hidden_seen cmr_bits seen_hidden) eqn:Hseen;
    [discriminate |].
  inversion Hconvert; subst.
  constructor.
  - apply hidden_seen_false_not_in. exact Hseen.
  - exact Hnodup.
Qed.

Lemma convert_raw_node_preserves_seen_hidden_256 :
  forall raw converted seen_hidden converted_node seen_hidden',
    Forall cmr_bits_length_256 (raw_node_hidden_cmrs raw) ->
    Forall cmr_bits_length_256 seen_hidden ->
    convert_raw_node converted seen_hidden raw =
      Some (converted_node, seen_hidden') ->
    Forall cmr_bits_length_256 seen_hidden'.
Proof.
  intros raw converted seen_hidden converted_node seen_hidden'
    Hraw_hidden Hseen_hidden Hconvert.
  destruct raw; simpl in Hconvert;
    try
      (repeat match goal with
      | H : context[match ?x with _ => _ end] |- _ =>
          destruct x eqn:?
      end;
      try discriminate;
      inversion Hconvert; subst; exact Hseen_hidden).
  destruct (hidden_seen cmr_bits seen_hidden) eqn:Hseen;
    [discriminate |].
  inversion Hconvert; subst.
  simpl in Hraw_hidden.
  inversion Hraw_hidden; subst.
  constructor; assumption.
Qed.

Lemma convert_raw_nodes_preserves_no_fail_from :
  forall raw converted seen_hidden converted' seen_hidden',
    raw_program_no_fail raw = true ->
    forallb converted_node_no_fail converted = true ->
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    forallb converted_node_no_fail converted' = true.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden'
      Hraw_no_fail Hconverted_no_fail Hconvert;
    simpl in Hconvert.
  - inversion Hconvert; subst. exact Hconverted_no_fail.
  - unfold raw_program_no_fail in Hraw_no_fail.
    simpl in Hraw_no_fail.
    apply andb_true_iff in Hraw_no_fail
      as [Hnode_no_fail Hrest_no_fail].
    destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    apply
      (IH
        (converted ++ [converted_node])
        seen_hidden_next
        converted'
        seen_hidden');
      [ exact Hrest_no_fail | | exact Hconvert ].
    rewrite forallb_app.
    simpl.
    rewrite Hconverted_no_fail.
    rewrite
      (@convert_raw_node_preserves_no_fail
        raw_node
        converted
        seen_hidden
        converted_node
        seen_hidden_next
        Hnode_no_fail
        Hnode).
    reflexivity.
Qed.

Lemma convert_raw_nodes_preserves_no_disconnect1_from :
  forall raw converted seen_hidden converted' seen_hidden',
    raw_program_no_disconnect1 raw = true ->
    forallb converted_node_no_disconnect1 converted = true ->
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    forallb converted_node_no_disconnect1 converted' = true.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden'
      Hraw_no_disconnect1 Hconverted_no_disconnect1 Hconvert;
    simpl in Hconvert.
  - inversion Hconvert; subst. exact Hconverted_no_disconnect1.
  - unfold raw_program_no_disconnect1 in Hraw_no_disconnect1.
    simpl in Hraw_no_disconnect1.
    apply andb_true_iff in Hraw_no_disconnect1
      as [Hnode_no_disconnect1 Hrest_no_disconnect1].
    destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    apply
      (IH
        (converted ++ [converted_node])
        seen_hidden_next
        converted'
        seen_hidden');
      [ exact Hrest_no_disconnect1 | | exact Hconvert ].
    rewrite forallb_app.
    simpl.
    rewrite Hconverted_no_disconnect1.
    rewrite
      (@convert_raw_node_preserves_no_disconnect1
        raw_node
        converted
        seen_hidden
        converted_node
        seen_hidden_next
        Hnode_no_disconnect1
        Hnode).
    reflexivity.
Qed.
