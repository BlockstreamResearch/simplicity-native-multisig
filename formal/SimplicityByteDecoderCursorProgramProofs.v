From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderCursorNaturalProofs.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma decode_raw_nodes_cursor_no_fail :
  forall count index cursor nodes rest,
    decode_raw_nodes_cursor count index cursor = Some (nodes, rest) ->
    raw_program_no_fail nodes = true.
Proof.
  induction count as [| count' IH];
    intros index cursor nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. reflexivity.
  - destruct (decode_raw_node_cursor index cursor)
      as [[node cursor'] |] eqn:Hnode; [| discriminate].
    destruct (decode_raw_nodes_cursor count' (S index) cursor')
      as [[nodes_tail rest_tail] |] eqn:Htail;
      [| discriminate].
    inversion Hdecode; subst.
    unfold raw_program_no_fail.
    simpl.
    apply andb_true_iff.
    split.
    + eapply decode_raw_node_cursor_no_fail. exact Hnode.
    + eapply IH. exact Htail.
Qed.

Lemma decode_raw_nodes_cursor_no_disconnect1 :
  forall count index cursor nodes rest,
    decode_raw_nodes_cursor count index cursor = Some (nodes, rest) ->
    raw_program_no_disconnect1 nodes = true.
Proof.
  induction count as [| count' IH];
    intros index cursor nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. reflexivity.
  - destruct (decode_raw_node_cursor index cursor)
      as [[node cursor'] |] eqn:Hnode; [| discriminate].
    destruct (decode_raw_nodes_cursor count' (S index) cursor')
      as [[nodes_tail rest_tail] |] eqn:Htail;
      [| discriminate].
    inversion Hdecode; subst.
    unfold raw_program_no_disconnect1.
    simpl.
    apply andb_true_iff.
    split.
    + eapply decode_raw_node_cursor_no_disconnect1. exact Hnode.
    + eapply IH. exact Htail.
Qed.

Lemma decode_raw_nodes_cursor_hidden_cmrs_256 :
  forall count index cursor nodes rest,
    decode_raw_nodes_cursor count index cursor = Some (nodes, rest) ->
    raw_program_hidden_cmrs_256 nodes.
Proof.
  induction count as [| count' IH];
    intros index cursor nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. constructor.
  - destruct (decode_raw_node_cursor index cursor)
      as [[head cursor'] |] eqn:Hhead; [| discriminate].
    destruct (decode_raw_nodes_cursor count' (S index) cursor')
      as [[tail rest_tail] |] eqn:Htail; [| discriminate].
    injection Hdecode as Hnodes Hrest.
    subst nodes.
    unfold raw_program_hidden_cmrs_256.
    simpl.
    apply Forall_app.
    split.
    + eapply decode_raw_node_cursor_hidden_cmrs_256.
      exact Hhead.
    + exact (IH (S index) cursor' tail rest_tail Htail).
Qed.

Theorem decode_raw_nodes_cursor_children_before_from :
  forall count index cursor nodes rest,
    decode_raw_nodes_cursor count index cursor = Some (nodes, rest) ->
    raw_program_children_before_from index nodes.
Proof.
  induction count as [| count' IH];
    intros index cursor nodes rest Hdecode offset node child Hnth Hchild;
    simpl in Hdecode.
  - inversion Hdecode; subst. destruct offset; discriminate.
  - destruct (decode_raw_node_cursor index cursor)
      as [[head cursor'] |] eqn:Hhead; [| discriminate].
    destruct (decode_raw_nodes_cursor count' (S index) cursor')
      as [[tail rest_tail] |] eqn:Htail; [| discriminate].
    injection Hdecode as Hnodes Hrest.
    subst nodes.
    destruct offset as [| offset'].
    + simpl in Hnth.
      inversion Hnth; subst.
      pose proof
        (@decode_raw_node_cursor_children_before
          index cursor node cursor' Hhead)
        as Hbefore.
      specialize (Hbefore child Hchild).
      lia.
    + simpl in Hnth.
      specialize
        (IH
          (S index)
          cursor'
          tail
          rest_tail
          Htail
          offset'
          node
          child
          Hnth
          Hchild).
      simpl.
      lia.
Qed.

Lemma decode_raw_nodes_cursor_length :
  forall count index cursor nodes rest,
    decode_raw_nodes_cursor count index cursor = Some (nodes, rest) ->
    length nodes = count.
Proof.
  induction count as [| count' IH];
    intros index cursor nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. reflexivity.
  - destruct (decode_raw_node_cursor index cursor)
      as [[node cursor'] |] eqn:Hnode; [| discriminate].
    destruct (decode_raw_nodes_cursor count' (S index) cursor')
      as [[nodes_tail rest_tail] |] eqn:Htail;
      [| discriminate].
    pose proof
      (IH (S index) cursor' nodes_tail rest_tail Htail)
      as Htail_length.
    injection Hdecode as Hnodes Hrest.
    subst nodes.
    simpl.
    rewrite Htail_length.
    reflexivity.
Qed.

Theorem decode_program_bytes_streaming_no_fail :
  forall bytes raw,
    decode_program_bytes_streaming bytes = Some raw ->
    raw_program_no_fail raw = true.
Proof.
  intros bytes raw Hdecode.
  unfold decode_program_bytes_streaming in Hdecode.
  destruct (decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes))
    as [[count cursor_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes_cursor count 0 cursor_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding_cursor padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_cursor_no_fail. exact Hnodes.
Qed.

Theorem decode_program_bytes_streaming_no_disconnect1 :
  forall bytes raw,
    decode_program_bytes_streaming bytes = Some raw ->
    raw_program_no_disconnect1 raw = true.
Proof.
  intros bytes raw Hdecode.
  unfold decode_program_bytes_streaming in Hdecode.
  destruct (decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes))
    as [[count cursor_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes_cursor count 0 cursor_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding_cursor padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_cursor_no_disconnect1. exact Hnodes.
Qed.

Theorem decode_program_bytes_streaming_raw_children_before :
  forall bytes raw,
    decode_program_bytes_streaming bytes = Some raw ->
    raw_program_children_before_from 0 raw.
Proof.
  intros bytes raw Hdecode.
  unfold decode_program_bytes_streaming in Hdecode.
  destruct (decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes))
    as [[count cursor_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes_cursor count 0 cursor_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding_cursor padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_cursor_children_before_from.
  exact Hnodes.
Qed.

Theorem decode_program_bytes_streaming_hidden_cmrs_256 :
  forall bytes raw,
    decode_program_bytes_streaming bytes = Some raw ->
    raw_program_hidden_cmrs_256 raw.
Proof.
  intros bytes raw Hdecode.
  unfold decode_program_bytes_streaming in Hdecode.
  destruct (decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes))
    as [[count cursor_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes_cursor count 0 cursor_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding_cursor padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_cursor_hidden_cmrs_256.
  exact Hnodes.
Qed.

Theorem decode_structural_program_bytes_streaming_raw_program :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    exists raw,
      decode_program_bytes_streaming bytes = Some raw /\
      validate_raw_program raw = Some program /\
      raw_canonical_order raw = true /\
      raw_program_children_before_from 0 raw.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  exists raw.
  split.
  - reflexivity.
  - split.
    + exact Hdecode.
    + split.
      * eapply validate_raw_program_canonical_order.
        exact Hdecode.
      * eapply decode_program_bytes_streaming_raw_children_before.
        exact Hraw.
Qed.

Theorem decode_structural_program_bytes_streaming_hidden_cmrs_256 :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    structural_program_hidden_cmrs_256 program.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_hidden_cmrs_256.
  - eapply decode_program_bytes_streaming_hidden_cmrs_256.
    exact Hraw.
  - exact Hdecode.
Qed.

Theorem decode_program_bytes_streaming_length_bound :
  forall bytes raw,
    decode_program_bytes_streaming bytes = Some raw ->
    length raw <= dag_len_max.
Proof.
  intros bytes raw Hdecode.
  unfold decode_program_bytes_streaming in Hdecode.
  destruct (decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes))
    as [[count cursor_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes_cursor count 0 cursor_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding_cursor padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst nodes.
  pose proof
    (@decode_natural_bound_cursor_some
      dag_len_max
      (cursor_start bytes)
      count
      cursor_after_count
      Hcount)
    as Hcount_bound.
  pose proof
    (@decode_raw_nodes_cursor_length
      count
      0
      cursor_after_count
      raw
      padding
      Hnodes)
    as Hlength.
  rewrite Hlength.
  exact Hcount_bound.
Qed.

Theorem decode_program_bytes_streaming_closed_padding :
  forall bytes raw,
    decode_program_bytes_streaming bytes = Some raw ->
    program_bytes_streaming_closed_padding bytes = true.
Proof.
  intros bytes raw Hdecode.
  unfold decode_program_bytes_streaming in Hdecode.
  unfold program_bytes_streaming_closed_padding.
  destruct (decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes))
    as [[count cursor_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes_cursor count 0 cursor_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding_cursor padding) eqn:Hpadding; [| discriminate].
  reflexivity.
Qed.

Theorem decode_structural_program_bytes_streaming_dag_well_formed :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    structural_program_dag_well_formed program = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_dag_well_formed.
  exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_streaming_child_references :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros bytes program Hdecode.
  apply structural_program_dag_well_formed_child_references.
  eapply decode_structural_program_bytes_streaming_dag_well_formed.
  exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_streaming_no_fail :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    structural_program_no_fail program = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_no_fail.
  - eapply decode_program_bytes_streaming_no_fail. exact Hraw.
  - exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_streaming_no_disconnect1 :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_no_disconnect1.
  - eapply decode_program_bytes_streaming_no_disconnect1. exact Hraw.
  - exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_streaming_closed_padding :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    program_bytes_streaming_closed_padding bytes = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  destruct (validate_raw_program raw) as [decoded_program |] eqn:Hvalidate;
    [| discriminate].
  eapply decode_program_bytes_streaming_closed_padding.
  exact Hraw.
Qed.

Theorem decode_structural_program_bytes_streaming_dag_len_bound :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    length (structural_nodes program) <= dag_len_max.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  pose proof
    (@validate_raw_program_length raw program Hdecode)
    as Hprogram_length.
  pose proof
    (@decode_program_bytes_streaming_length_bound bytes raw Hraw)
    as Hraw_bound.
  rewrite Hprogram_length.
  exact Hraw_bound.
Qed.
