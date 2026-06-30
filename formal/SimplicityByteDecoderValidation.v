From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderConversionProperties.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma convert_raw_nodes_preserves_seen_hidden_NoDup :
  forall raw converted seen_hidden converted' seen_hidden',
    NoDup seen_hidden ->
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    NoDup seen_hidden'.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden'
      Hnodup Hconvert; simpl in Hconvert.
  - inversion Hconvert; subst. exact Hnodup.
  - destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    apply
      (IH
        (converted ++ [converted_node])
        seen_hidden_next
        converted'
        seen_hidden');
      [| exact Hconvert].
    eapply convert_raw_node_preserves_seen_hidden_NoDup.
    + exact Hnodup.
    + exact Hnode.
Qed.

Lemma convert_raw_nodes_preserves_seen_hidden_256 :
  forall raw converted seen_hidden converted' seen_hidden',
    raw_program_hidden_cmrs_256 raw ->
    Forall cmr_bits_length_256 seen_hidden ->
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    Forall cmr_bits_length_256 seen_hidden'.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden'
      Hraw_hidden Hseen_hidden Hconvert; simpl in Hconvert.
  - inversion Hconvert; subst. exact Hseen_hidden.
  - destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    unfold raw_program_hidden_cmrs_256 in Hraw_hidden.
    simpl in Hraw_hidden.
    apply Forall_app in Hraw_hidden as [Hnode_hidden Hrest_hidden].
    apply
      (IH
        (converted ++ [converted_node])
        seen_hidden_next
        converted'
        seen_hidden');
      [ exact Hrest_hidden | | exact Hconvert ].
    eapply convert_raw_node_preserves_seen_hidden_256.
    + exact Hnode_hidden.
    + exact Hseen_hidden.
    + exact Hnode.
Qed.

Lemma convert_raw_nodes_backrefs_are_nodes_from :
  forall raw converted seen_hidden converted' seen_hidden',
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    exists suffix,
      converted' = converted ++ suffix /\
      converted_nodes_backrefs_are_nodesb_from converted suffix = true.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden' Hconvert;
    simpl in Hconvert.
  - inversion Hconvert; subst.
    exists [].
    split.
    + rewrite app_nil_r. reflexivity.
    + reflexivity.
  - destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    pose proof
      (@convert_raw_node_backrefs_are_nodes
        raw_node
        converted
        seen_hidden
        converted_node
        seen_hidden_next
        Hnode)
      as Hnode_backrefs.
    specialize
      (IH (converted ++ [converted_node]) seen_hidden_next
        converted' seen_hidden' Hconvert)
      as [suffix [Hsuffix_eq Hsuffix_backrefs]].
    exists (converted_node :: suffix).
    split.
    + rewrite Hsuffix_eq.
      rewrite <- app_assoc.
      reflexivity.
    + simpl.
      rewrite Hnode_backrefs.
      simpl.
      exact Hsuffix_backrefs.
Qed.

Lemma converted_node_hidden_cmrs_rev_self :
  forall node,
    rev (converted_node_hidden_cmrs node) = converted_node_hidden_cmrs node.
Proof.
  intros node.
  destruct node; reflexivity.
Qed.

Lemma convert_raw_nodes_hidden_seen_relation :
  forall raw converted seen_hidden converted' seen_hidden',
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    exists suffix,
      converted' = converted ++ suffix /\
      rev (converted_nodes_hidden_cmrs suffix) ++ seen_hidden = seen_hidden'.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden' Hconvert;
    simpl in Hconvert.
  - inversion Hconvert; subst.
    exists [].
    split.
    + rewrite app_nil_r. reflexivity.
    + reflexivity.
  - destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    pose proof
      (@convert_raw_node_hidden_seen_relation
        raw_node
        converted
        seen_hidden
        converted_node
        seen_hidden_next
        Hnode)
      as Hnode_seen.
    specialize
      (IH
        (converted ++ [converted_node])
        seen_hidden_next
        converted'
        seen_hidden'
        Hconvert)
      as [suffix [Hsuffix_eq Hsuffix_seen]].
    exists (converted_node :: suffix).
    split.
    + rewrite Hsuffix_eq.
      rewrite <- app_assoc.
      reflexivity.
    + simpl.
      rewrite rev_app_distr.
      rewrite converted_node_hidden_cmrs_rev_self.
      rewrite <- app_assoc.
      rewrite Hnode_seen.
      exact Hsuffix_seen.
Qed.

Lemma converted_nodes_backrefs_are_nodesb_from_child_sound :
  forall prefix nodes parent node child,
    converted_nodes_backrefs_are_nodesb_from prefix nodes = true ->
    nth_error nodes parent = Some (CNode node) ->
    In child (structural_node_children node) ->
    exists child_node,
      nth_error (prefix ++ nodes) child = Some (CNode child_node) /\
      child < length prefix + parent.
Proof.
  intros prefix nodes.
  revert prefix.
  induction nodes as [| head rest IH];
    intros prefix parent node child Hbackrefs Hparent Hchild_in;
    destruct parent; simpl in Hparent; try discriminate.
  - apply andb_true_iff in Hbackrefs as [Hhead_backrefs _].
    inversion Hparent; subst head.
    simpl in Hhead_backrefs.
    unfold structural_node_backrefs_are_nodesb in Hhead_backrefs.
    rewrite forallb_forall in Hhead_backrefs.
    pose proof (Hhead_backrefs child Hchild_in) as Hchild_is_node.
    pose proof
      (@converted_child_is_nodeb_sound prefix child Hchild_is_node)
      as [child_node Hchild_node].
    exists child_node.
    split.
    + eapply nth_error_app_prefix. exact Hchild_node.
    + pose proof
        (@nth_error_some_length
          ConvertedNode
          prefix
          child
          (CNode child_node)
          Hchild_node)
        as Hchild_lt_prefix.
      lia.
  - apply andb_true_iff in Hbackrefs as [_ Hrest_backrefs].
    pose proof
      (IH
        (prefix ++ [head])
        parent
        node
        child
        Hrest_backrefs
        Hparent
        Hchild_in)
      as [child_node [Hchild_node Hchild_lt]].
    exists child_node.
    split.
    + rewrite <- app_assoc in Hchild_node.
      simpl in Hchild_node.
      exact Hchild_node.
    + rewrite length_app in Hchild_lt.
      simpl in Hchild_lt.
      lia.
Qed.

Definition validate_raw_program (raw : list RawNode) :
    option StructuralProgram :=
  match raw with
  | [] => None
  | _ =>
      if raw_canonical_order raw then
        match convert_raw_nodes raw [] [] with
        | None => None
        | Some (converted, _) =>
            let root := pred (length raw) in
            match nth_error converted root with
            | Some (CNode _) =>
                Some {| structural_nodes := converted; structural_root := root |}
            | _ => None
            end
        end
      else None
  end.
