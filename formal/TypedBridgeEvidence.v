From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import SimplicityByteDecoder TypedBridgeCore.
Import ListNotations.
Set Implicit Arguments.
Set Strict Implicit.
Lemma bridge_type_eqb_true :
  forall lhs rhs,
    bridge_type_eqb lhs rhs = true ->
    lhs = rhs.
Proof.
  induction lhs as [| lhs_left IHleft lhs_right IHright
                    | lhs_left IHleft lhs_right IHright
                    | lhs_tag];
    intros rhs Heq; destruct rhs; simpl in Heq; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Heq as [Hleft Hright].
    apply IHleft in Hleft.
    apply IHright in Hright.
    subst. reflexivity.
  - apply andb_true_iff in Heq as [Hleft Hright].
    apply IHleft in Hleft.
    apply IHright in Hright.
    subst. reflexivity.
  - apply Nat.eqb_eq in Heq. subst. reflexivity.
Qed.
Lemma bridge_arrow_eqb_true :
  forall lhs rhs,
    bridge_arrow_eqb lhs rhs = true ->
    lhs = rhs.
Proof.
  intros lhs rhs Heq.
  unfold bridge_arrow_eqb in Heq.
  apply andb_true_iff in Heq as [Hsource Htarget].
  apply bridge_type_eqb_true in Hsource.
  apply bridge_type_eqb_true in Htarget.
  destruct lhs as [lhs_source lhs_target].
  destruct rhs as [rhs_source rhs_target].
  simpl in *. subst. reflexivity.
Qed.
Lemma child_arrow_eqb_true :
  forall prefix index expected,
    child_arrow_eqb prefix index expected = true ->
    child_has_arrow prefix index expected.
Proof.
  intros prefix index expected Hcheck.
  unfold child_arrow_eqb in Hcheck.
  unfold child_has_arrow.
  destruct (typed_prefix_lookup prefix index) as [actual |] eqn:Hlookup;
    [| discriminate].
  apply bridge_arrow_eqb_true in Hcheck.
  subst actual.
  reflexivity.
Qed.
Theorem typecheck_structural_node_sound :
  forall hooks prefix node arrow,
    typecheck_structural_node hooks prefix node arrow = true ->
    structural_node_type_evidence hooks prefix node arrow.
Proof.
  intros hooks prefix node arrow Hcheck.
  destruct arrow as [source target].
  destruct node as
    [| | child | child | child | child | lhs rhs | lhs rhs
     | lhs hidden_cmr | hidden_cmr rhs | lhs rhs | lhs
     | lhs rhs | | entropy_bits | jet | encoded_width value_bits];
    simpl in Hcheck; simpl.
  - apply bridge_type_eqb_true. exact Hcheck.
  - apply bridge_type_eqb_true. exact Hcheck.
  - destruct target as [| sum_left sum_right | target_left target_right | target_tag];
      try discriminate.
    exists sum_left, sum_right.
    split; [reflexivity |].
    apply child_arrow_eqb_true. exact Hcheck.
  - destruct target as [| sum_left sum_right | target_left target_right | target_tag];
      try discriminate.
    exists sum_left, sum_right.
    split; [reflexivity |].
    apply child_arrow_eqb_true. exact Hcheck.
  - destruct source as [| source_left source_right | prod_left prod_right | source_tag];
      try discriminate.
    exists prod_left, prod_right.
    split; [reflexivity |].
    apply child_arrow_eqb_true. exact Hcheck.
  - destruct source as [| source_left source_right | prod_left prod_right | source_tag];
      try discriminate.
    exists prod_left, prod_right.
    split; [reflexivity |].
    apply child_arrow_eqb_true. exact Hcheck.
  - destruct (typed_prefix_lookup prefix lhs) as [lhs_arrow |] eqn:Hlhs;
      [| discriminate].
    destruct (typed_prefix_lookup prefix rhs) as [rhs_arrow |] eqn:Hrhs;
      [| discriminate].
    apply andb_true_iff in Hcheck as [Hrest Htarget].
    apply andb_true_iff in Hrest as [Hsource Hmiddle].
    apply bridge_type_eqb_true in Hsource.
    apply bridge_type_eqb_true in Hmiddle.
    apply bridge_type_eqb_true in Htarget.
    exists lhs_arrow, rhs_arrow.
    repeat split; assumption.
  - destruct source as [| source_left source_right | source_left source_right | source_tag];
      try discriminate.
    destruct source_left as
      [| sum_left sum_right | sum_left sum_right | sum_tag];
      try discriminate.
    apply andb_true_iff in Hcheck as [Hlhs Hrhs].
    exists sum_left, sum_right, source_right.
    repeat split; try reflexivity.
    + apply child_arrow_eqb_true. exact Hlhs.
    + apply child_arrow_eqb_true. exact Hrhs.
  - destruct source as [| source_left source_right | source_left source_right | source_tag];
      try discriminate.
    destruct source_left as
      [| sum_left sum_right | sum_left sum_right | sum_tag];
      try discriminate.
    exists sum_left, sum_right, source_right.
    split; [reflexivity |].
    apply child_arrow_eqb_true. exact Hcheck.
  - destruct source as [| source_left source_right | source_left source_right | source_tag];
      try discriminate.
    destruct source_left as
      [| sum_left sum_right | sum_left sum_right | sum_tag];
      try discriminate.
    exists sum_left, sum_right, source_right.
    split; [reflexivity |].
    apply child_arrow_eqb_true. exact Hcheck.
  - destruct target as [| target_left target_right | prod_left prod_right | target_tag];
      try discriminate.
    apply andb_true_iff in Hcheck as [Hlhs Hrhs].
    exists prod_left, prod_right.
    repeat split; try reflexivity.
    + apply child_arrow_eqb_true. exact Hlhs.
    + apply child_arrow_eqb_true. exact Hrhs.
  - destruct (typed_prefix_lookup prefix lhs) as [lhs_arrow |] eqn:Hlhs;
      [| discriminate].
    exists lhs_arrow.
    split.
    + reflexivity.
    + exact Hcheck.
  - destruct (typed_prefix_lookup prefix lhs) as [lhs_arrow |] eqn:Hlhs;
      [| discriminate].
    destruct (typed_prefix_lookup prefix rhs) as [rhs_arrow |] eqn:Hrhs;
      [| discriminate].
    exists lhs_arrow, rhs_arrow.
    repeat split; try reflexivity; assumption.
  - exact Hcheck.
  - exact Hcheck.
  - apply bridge_arrow_eqb_true in Hcheck.
    exact Hcheck.
  - exact Hcheck.
Qed.
Lemma check_typed_nodes_from_type_evidence :
  forall hooks prefix nodes types,
    check_typed_nodes_from hooks prefix nodes types = true ->
    typed_nodes_type_evidence_from hooks prefix nodes types.
Proof.
  intros hooks prefix nodes.
  revert prefix.
  induction nodes as [| node rest_nodes IH]; intros prefix types Hcheck.
  - destruct types as [| type_entry rest_types]; simpl in Hcheck;
      [exact I | discriminate].
  - destruct types as [| type_entry rest_types]; simpl in Hcheck.
    + destruct node; discriminate.
    + destruct node as [structural_node | hidden_cmr].
      * destruct type_entry as [arrow |]; simpl in Hcheck; [| discriminate].
        apply andb_true_iff in Hcheck as [Hnode Hrest].
        split.
        -- apply typecheck_structural_node_sound. exact Hnode.
        -- eapply IH. exact Hrest.
      * destruct type_entry as [arrow |]; simpl in Hcheck; [discriminate |].
        eapply IH. exact Hcheck.
Qed.
Lemma typed_nodes_type_evidence_from_nth :
  forall hooks prefix nodes types index node arrow,
    typed_nodes_type_evidence_from hooks prefix nodes types ->
    nth_error nodes index = Some (CNode node) ->
    nth_error types index = Some (Some arrow) ->
    structural_node_type_evidence hooks (prefix ++ firstn index types) node arrow.
Proof.
  intros hooks prefix nodes.
  revert prefix.
  induction nodes as [| node_entry rest_nodes IH];
    intros prefix types index target_node target_arrow Hevidence Hnode Htype.
  - destruct index; discriminate Hnode.
  - destruct types as [| type_entry rest_types]; simpl in Hevidence.
    + destruct index; discriminate Htype.
    + destruct index as [| index'].
      * simpl in Hnode, Htype.
        destruct node_entry as [structural_node | hidden_cmr];
          destruct type_entry as [head_arrow |];
          simpl in Hevidence; try contradiction; try discriminate.
        inversion Hnode; inversion Htype; subst.
        rewrite app_nil_r.
        exact (proj1 Hevidence).
      * simpl in Hnode, Htype.
        destruct node_entry as [structural_node | hidden_cmr];
          destruct type_entry as [head_arrow |];
          simpl in Hevidence; try contradiction; try discriminate.
        -- specialize
             (IH
               (prefix ++ [Some head_arrow])
               rest_types
               index'
               target_node
               target_arrow
               (proj2 Hevidence)
               Hnode
               Htype).
           rewrite <- app_assoc in IH.
           simpl in IH.
           exact IH.
        -- specialize
             (IH
               (prefix ++ [None])
               rest_types
               index'
               target_node
               target_arrow
               Hevidence
               Hnode
               Htype).
           rewrite <- app_assoc in IH.
           simpl in IH.
           exact IH.
Qed.
Lemma check_typed_nodes_from_length :
  forall hooks prefix nodes types,
    check_typed_nodes_from hooks prefix nodes types = true ->
    length nodes = length types.
Proof.
  intros hooks prefix nodes.
  revert prefix.
  induction nodes as [| node rest_nodes IH]; intros prefix types Hcheck.
  - destruct types as [| type_entry rest_types]; simpl in Hcheck;
      [reflexivity | discriminate].
  - destruct types as [| type_entry rest_types]; simpl in Hcheck.
    + destruct node; discriminate.
    + destruct node as [structural_node | hidden_cmr].
      * destruct type_entry as [arrow |]; simpl in Hcheck; [| discriminate].
        apply andb_true_iff in Hcheck as [_ Hrest].
        simpl. f_equal. eapply IH. exact Hrest.
      * destruct type_entry as [arrow |]; simpl in Hcheck; [discriminate |].
        simpl. f_equal. eapply IH. exact Hcheck.
Qed.

Lemma check_typed_nodes_from_shape :
  forall hooks prefix nodes types,
    check_typed_nodes_from hooks prefix nodes types = true ->
    Forall2 typed_entry_matches_node nodes types.
Proof.
  intros hooks prefix nodes.
  revert prefix.
  induction nodes as [| node rest_nodes IH]; intros prefix types Hcheck.
  - destruct types as [| type_entry rest_types]; simpl in Hcheck;
      [constructor | discriminate].
  - destruct types as [| type_entry rest_types]; simpl in Hcheck.
    + destruct node; discriminate.
    + destruct node as [structural_node | hidden_cmr].
      * destruct type_entry as [arrow |]; simpl in Hcheck; [| discriminate].
        apply andb_true_iff in Hcheck as [_ Hrest].
        constructor.
        -- simpl. exact I.
        -- eapply IH. exact Hrest.
      * destruct type_entry as [arrow |]; simpl in Hcheck; [discriminate |].
        constructor.
        -- simpl. exact I.
        -- eapply IH. exact Hcheck.
Qed.

Lemma typed_table_matches_cnode_has_arrow :
  forall nodes types index node,
    Forall2 typed_entry_matches_node nodes types ->
    nth_error nodes index = Some (CNode node) ->
    exists arrow,
      nth_error types index = Some (Some arrow).
Proof.
  intros nodes types index node Hmatches.
  revert index node.
  induction Hmatches as [| node_entry type_entry nodes types Hhead Htail IH];
    intros index target_node Hnth; simpl in Hnth.
  - destruct index; discriminate Hnth.
  - destruct index as [| index'].
    + inversion Hnth; subst node_entry.
      destruct type_entry as [arrow |]; simpl in Hhead; try contradiction.
      exists arrow. reflexivity.
    + eapply IH. exact Hnth.
Qed.

Theorem typed_table_child_references_have_arrows :
  forall program types,
    structural_program_child_references_are_backward_nodes program ->
    typed_table_matches_program program types ->
    typed_program_child_references_have_arrows program types.
Proof.
  intros program types Hchildren Htypes.
  unfold typed_program_child_references_have_arrows.
  intros parent node child Hparent Hchild.
  pose proof (Hchildren parent node child Hparent Hchild)
    as [child_node [Hchild_node Hchild_lt]].
  unfold typed_table_matches_program in Htypes.
  pose proof
    (@typed_table_matches_cnode_has_arrow
      (structural_nodes program)
      types
      child
      child_node
      Htypes
      Hchild_node)
    as [child_arrow Hchild_arrow].
  exists child_node.
  exists child_arrow.
  repeat split; assumption.
Qed.

Theorem typed_root_entry_has_arrow :
  forall program types root_arrow,
    structural_program_dag_well_formed program = true ->
    typed_root_entry program types = Some root_arrow ->
    typed_program_root_has_arrow program types root_arrow.
Proof.
  intros program types root_arrow Hdag Hroot_entry.
  unfold structural_program_dag_well_formed in Hdag.
  destruct (nth_error (structural_nodes program) (structural_root program))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  unfold typed_root_entry in Hroot_entry.
  destruct (nth_error types (structural_root program))
    as [[actual_root_arrow |] |] eqn:Htyped_root; try discriminate.
  inversion Hroot_entry; subst actual_root_arrow.
  exists root_node.
  split.
  - exact Hroot.
  - exact Htyped_root.
Qed.

Theorem check_typed_structural_program_sound :
  forall hooks program types root_arrow,
    check_typed_structural_program hooks program types root_arrow = true ->
    TypedStructuralProgramEvidence hooks program types root_arrow.
Proof.
  intros hooks program types root_arrow Hcheck.
  unfold check_typed_structural_program in Hcheck.
  apply andb_true_iff in Hcheck as [Hnodes Hroot].
  destruct (typed_root_entry program types) as [actual_root_arrow |]
    eqn:Hroot_entry; [| discriminate].
  apply bridge_arrow_eqb_true in Hroot.
  subst actual_root_arrow.
  constructor.
  - exact Hnodes.
  - unfold typed_program_nodes_have_type_evidence.
    eapply check_typed_nodes_from_type_evidence.
    exact Hnodes.
  - eapply check_typed_nodes_from_length.
    exact Hnodes.
  - unfold typed_table_matches_program.
    eapply check_typed_nodes_from_shape.
    exact Hnodes.
  - exact Hroot_entry.
Qed.

Theorem typed_program_node_has_type_evidence :
  forall hooks program types root_arrow index node arrow,
    TypedStructuralProgramEvidence hooks program types root_arrow ->
    nth_error (structural_nodes program) index = Some (CNode node) ->
    nth_error types index = Some (Some arrow) ->
    structural_node_type_evidence hooks (firstn index types) node arrow.
Proof.
  intros hooks program types root_arrow index node arrow Htyped Hnode Htype.
  pose proof (typed_node_type_evidence Htyped) as Hevidence.
  unfold typed_program_nodes_have_type_evidence in Hevidence.
  pose proof
    (@typed_nodes_type_evidence_from_nth
      hooks
      []
      (structural_nodes program)
      types
      index
      node
      arrow
      Hevidence
      Hnode
      Htype) as Hnode_evidence.
  exact Hnode_evidence.
Qed.

Record TypedByteBridgeEvidence
    (hooks : TypeHooks)
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : Prop := {
  typed_byte_dag :
    structural_program_dag_well_formed program = true;
  typed_byte_child_references :
    structural_program_child_references_are_backward_nodes program;
  typed_byte_child_arrows :
    typed_program_child_references_have_arrows program types;
  typed_byte_root_arrow :
    typed_program_root_has_arrow program types root_arrow;
  typed_byte_no_fail :
    structural_program_no_fail program = true;
  typed_byte_no_fail_nodes :
    forall index entropy_bits,
      nth_error (structural_nodes program) index =
        Some (CNode (SFail entropy_bits)) ->
      False;
  typed_byte_no_disconnect1 :
    structural_program_no_disconnect1 program = true;
  typed_byte_no_disconnect1_nodes :
    forall index child,
      nth_error (structural_nodes program) index =
        Some (CNode (SDisconnect1 child)) ->
      False;
  typed_byte_program :
    TypedStructuralProgramEvidence hooks program types root_arrow
}.

Theorem check_typed_structural_program_with_byte_evidence :
  forall hooks program types root_arrow,
    structural_program_dag_well_formed program = true ->
    structural_program_no_fail program = true ->
    structural_program_no_disconnect1 program = true ->
    check_typed_structural_program hooks program types root_arrow = true ->
    TypedByteBridgeEvidence hooks program types root_arrow.
Proof.
  intros hooks program types root_arrow Hdag Hno_fail Hno_disconnect1 Htyped.
  pose proof
    (@check_typed_structural_program_sound hooks program types root_arrow Htyped)
    as Htyped_evidence.
  pose proof
    (@structural_program_dag_well_formed_child_references program Hdag)
    as Hchildren.
  constructor.
  - exact Hdag.
  - exact Hchildren.
  - eapply typed_table_child_references_have_arrows.
    + exact Hchildren.
    + exact (typed_table_shape Htyped_evidence).
  - eapply typed_root_entry_has_arrow.
    + exact Hdag.
    + exact (typed_root_checked Htyped_evidence).
  - exact Hno_fail.
  - intros index entropy_bits Hnth.
    eapply structural_program_no_fail_no_sfail_node.
    + exact Hno_fail.
    + exact Hnth.
  - exact Hno_disconnect1.
  - intros index child Hnth.
    eapply structural_program_no_disconnect1_no_sdisconnect1_node.
    + exact Hno_disconnect1.
    + exact Hnth.
  - exact Htyped_evidence.
Qed.
