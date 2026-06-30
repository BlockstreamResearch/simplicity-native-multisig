From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderCursorParser.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma decode_raw_nodes_no_fail :
  forall count index bits nodes rest,
    decode_raw_nodes count index bits = Some (nodes, rest) ->
    raw_program_no_fail nodes = true.
Proof.
  induction count as [| count' IH];
    intros index bits nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. reflexivity.
  - destruct (decode_raw_node index bits) as [[node bits'] |] eqn:Hnode;
      [| discriminate].
    destruct (decode_raw_nodes count' (S index) bits')
      as [[nodes_tail rest_tail] |] eqn:Htail;
      [| discriminate].
    inversion Hdecode; subst.
    unfold raw_program_no_fail.
    simpl.
    apply andb_true_iff.
    split.
    + eapply decode_raw_node_no_fail. exact Hnode.
    + eapply IH. exact Htail.
Qed.

Lemma decode_raw_nodes_no_disconnect1 :
  forall count index bits nodes rest,
    decode_raw_nodes count index bits = Some (nodes, rest) ->
    raw_program_no_disconnect1 nodes = true.
Proof.
  induction count as [| count' IH];
    intros index bits nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. reflexivity.
  - destruct (decode_raw_node index bits) as [[node bits'] |] eqn:Hnode;
      [| discriminate].
    destruct (decode_raw_nodes count' (S index) bits')
      as [[nodes_tail rest_tail] |] eqn:Htail;
      [| discriminate].
    inversion Hdecode; subst.
    unfold raw_program_no_disconnect1.
    simpl.
    apply andb_true_iff.
    split.
    + eapply decode_raw_node_no_disconnect1. exact Hnode.
    + eapply IH. exact Htail.
Qed.

Theorem decode_raw_nodes_children_before_from :
  forall count index bits nodes rest,
    decode_raw_nodes count index bits = Some (nodes, rest) ->
    raw_program_children_before_from index nodes.
Proof.
  induction count as [| count' IH];
    intros index bits nodes rest Hdecode offset node child Hnth Hchild;
    simpl in Hdecode.
  - inversion Hdecode; subst. destruct offset; discriminate.
  - destruct (decode_raw_node index bits) as [[head bits'] |] eqn:Hhead;
      [| discriminate].
    destruct (decode_raw_nodes count' (S index) bits')
      as [[tail rest_tail] |] eqn:Htail; [| discriminate].
    injection Hdecode as Hnodes Hrest.
    subst nodes.
    destruct offset as [| offset'].
    + simpl in Hnth.
      inversion Hnth; subst.
      pose proof
        (@decode_raw_node_children_before index bits node bits' Hhead)
        as Hbefore.
      specialize (Hbefore child Hchild).
      lia.
    + simpl in Hnth.
      specialize
        (IH
          (S index)
          bits'
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

Theorem decode_raw_nodes_hidden_cmrs_256 :
  forall count index bits nodes rest,
    decode_raw_nodes count index bits = Some (nodes, rest) ->
    raw_program_hidden_cmrs_256 nodes.
Proof.
  induction count as [| count' IH];
    intros index bits nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. constructor.
  - destruct (decode_raw_node index bits) as [[head bits'] |] eqn:Hhead;
      [| discriminate].
    destruct (decode_raw_nodes count' (S index) bits')
      as [[tail rest_tail] |] eqn:Htail; [| discriminate].
    injection Hdecode as Hnodes Hrest.
    subst nodes.
    unfold raw_program_hidden_cmrs_256.
    simpl.
    apply Forall_app.
    split.
    + eapply decode_raw_node_hidden_cmrs_256.
      exact Hhead.
    + exact (IH (S index) bits' tail rest_tail Htail).
Qed.

Definition close_padding (bits : list bool) : bool :=
  (length bits <? 8) && all_false bits.

Definition decode_program_bits (bits : list bool) :
    option (list RawNode) :=
  match decode_natural_bound (Some dag_len_max) bits with
  | None => None
  | Some (count, bits') =>
      match decode_raw_nodes count 0 bits' with
      | None => None
      | Some (nodes, rest) =>
          if close_padding rest then Some nodes else None
      end
  end.

Definition program_bytes_closed_padding (bytes : list byte) : bool :=
  match decode_natural_bound (Some dag_len_max) (bytes_to_bits bytes) with
  | None => false
  | Some (count, bits') =>
      match decode_raw_nodes count 0 bits' with
      | None => false
      | Some (_, rest) => close_padding rest
      end
  end.

Theorem close_padding_sound :
  forall padding,
    close_padding padding = true ->
    length padding < 8 /\ all_false padding = true.
Proof.
  intros padding Hpadding.
  unfold close_padding in Hpadding.
  apply andb_true_iff in Hpadding as [Hlength Hall_false].
  apply Nat.ltb_lt in Hlength.
  split; assumption.
Qed.

Theorem decode_program_bits_no_fail :
  forall bits raw,
    decode_program_bits bits = Some raw ->
    raw_program_no_fail raw = true.
Proof.
  intros bits raw Hdecode.
  unfold decode_program_bits in Hdecode.
  destruct (decode_natural_bound (Some dag_len_max) bits)
    as [[count bits_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes count 0 bits_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_no_fail. exact Hnodes.
Qed.

Theorem decode_program_bits_no_disconnect1 :
  forall bits raw,
    decode_program_bits bits = Some raw ->
    raw_program_no_disconnect1 raw = true.
Proof.
  intros bits raw Hdecode.
  unfold decode_program_bits in Hdecode.
  destruct (decode_natural_bound (Some dag_len_max) bits)
    as [[count bits_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes count 0 bits_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_no_disconnect1. exact Hnodes.
Qed.

Theorem decode_program_bits_raw_children_before :
  forall bits raw,
    decode_program_bits bits = Some raw ->
    raw_program_children_before_from 0 raw.
Proof.
  intros bits raw Hdecode.
  unfold decode_program_bits in Hdecode.
  destruct (decode_natural_bound (Some dag_len_max) bits)
    as [[count bits_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes count 0 bits_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_children_before_from.
  exact Hnodes.
Qed.

Theorem decode_program_bits_hidden_cmrs_256 :
  forall bits raw,
    decode_program_bits bits = Some raw ->
    raw_program_hidden_cmrs_256 raw.
Proof.
  intros bits raw Hdecode.
  unfold decode_program_bits in Hdecode.
  destruct (decode_natural_bound (Some dag_len_max) bits)
    as [[count bits_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes count 0 bits_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_raw_nodes_hidden_cmrs_256.
  exact Hnodes.
Qed.

Theorem decode_program_bits_close_padding :
  forall bits raw,
    decode_program_bits bits = Some raw ->
    exists count bits_after_count padding,
      decode_natural_bound (Some dag_len_max) bits =
        Some (count, bits_after_count) /\
      count <= dag_len_max /\
      decode_raw_nodes count 0 bits_after_count = Some (raw, padding) /\
      close_padding padding = true.
Proof.
  intros bits raw Hdecode.
  unfold decode_program_bits in Hdecode.
  destruct (decode_natural_bound (Some dag_len_max) bits)
    as [[count bits_after_count] |]
    eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes count 0 bits_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding padding) eqn:Hpadding; [| discriminate].
  inversion Hdecode; subst nodes.
  exists count, bits_after_count, padding.
  repeat split; try assumption.
  eapply decode_natural_bound_some.
  exact Hcount.
Qed.

Lemma decode_raw_nodes_length :
  forall count index bits nodes rest,
    decode_raw_nodes count index bits = Some (nodes, rest) ->
    length nodes = count.
Proof.
  induction count as [| count' IH];
    intros index bits nodes rest Hdecode; simpl in Hdecode.
  - inversion Hdecode; subst. reflexivity.
  - destruct (decode_raw_node index bits) as [[node bits'] |] eqn:Hnode;
      [| discriminate].
    destruct (decode_raw_nodes count' (S index) bits')
      as [[nodes_tail rest_tail] |] eqn:Htail;
      [| discriminate].
    pose proof
      (IH (S index) bits' nodes_tail rest_tail Htail)
      as Htail_length.
    injection Hdecode as Hnodes Hrest.
    subst nodes.
    simpl.
    rewrite Htail_length.
    reflexivity.
Qed.

Theorem decode_program_bits_length_bound :
  forall bits raw,
    decode_program_bits bits = Some raw ->
    length raw <= dag_len_max.
Proof.
  intros bits raw Hdecode.
  pose proof
    (@decode_program_bits_close_padding bits raw Hdecode)
    as [count [bits_after_count [padding
      [Hcount [Hcount_bound [Hnodes _Hpadding]]]]]].
  pose proof
    (@decode_raw_nodes_length
      count 0 bits_after_count raw padding Hnodes)
    as Hlength.
  rewrite Hlength.
  exact Hcount_bound.
Qed.
