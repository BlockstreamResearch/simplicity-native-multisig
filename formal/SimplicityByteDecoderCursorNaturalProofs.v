From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderDecodeStructuralProperties.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition program_bytes_streaming_closed_padding (bytes : list byte) : bool :=
  match decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes) with
  | None => false
  | Some (count, cursor') =>
      match decode_raw_nodes_cursor count 0 cursor' with
      | None => false
      | Some (_, rest) => close_padding_cursor rest
      end
  end.

Lemma decode_natural_bound_cursor_some :
  forall max cursor n rest,
    decode_natural_bound_cursor (Some max) cursor = Some (n, rest) ->
    n <= max.
Proof.
  intros max cursor n rest Hdecode.
  unfold decode_natural_bound_cursor in Hdecode.
  destruct (decode_natural_cursor cursor) as [[decoded rest'] |]
    eqn:Hnatural; [| discriminate].
  destruct (decoded <=? max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  apply Nat.leb_le in Hbound.
  exact Hbound.
Qed.

Lemma read_natural_payload_cursor_positive :
  forall width cursor n rest,
    read_natural_payload_cursor width cursor = Some (n, rest) ->
    1 <= n.
Proof.
  intros width cursor n rest Hread.
  unfold read_natural_payload_cursor in Hread.
  destruct (read_bits_nat_cursor width cursor) as [[suffix rest'] |]
    eqn:Hbits; [| discriminate].
  inversion Hread; subst.
  pose proof (pow2_positive width) as Hpow.
  lia.
Qed.

Lemma decode_natural_loop_cursor_positive :
  forall fuel depth width cursor n rest,
    decode_natural_loop_cursor fuel depth width cursor = Some (n, rest) ->
    1 <= n.
Proof.
  induction fuel as [| fuel IH];
    intros depth width cursor n rest Hdecode; simpl in Hdecode.
  - discriminate.
  - destruct (read_natural_payload_cursor width cursor)
      as [[payload cursor_after_payload] |] eqn:Hpayload;
      [| discriminate].
    destruct depth as [| depth'].
    + inversion Hdecode; subst.
      eapply read_natural_payload_cursor_positive.
      exact Hpayload.
    + destruct (31 <? payload) eqn:Hpayload_bound; [discriminate |].
      eapply IH.
      exact Hdecode.
Qed.

Theorem decode_natural_cursor_some_positive :
  forall cursor n rest,
    decode_natural_cursor cursor = Some (n, rest) ->
    1 <= n.
Proof.
  intros cursor n rest Hdecode.
  unfold decode_natural_cursor in Hdecode.
  destruct (decode_natural_unbounded_cursor cursor)
    as [[decoded rest'] |] eqn:Hunbounded; [| discriminate].
  destruct (decoded <=? natural_max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  unfold decode_natural_unbounded_cursor in Hunbounded.
  destruct (read_unary_depth_cursor cursor) as [[depth cursor_after_depth] |]
    eqn:Hdepth; [| discriminate].
  eapply decode_natural_loop_cursor_positive.
  exact Hunbounded.
Qed.

Lemma decode_natural_bound_cursor_some_positive :
  forall max cursor n rest,
    decode_natural_bound_cursor (Some max) cursor = Some (n, rest) ->
    1 <= n.
Proof.
  intros max cursor n rest Hdecode.
  unfold decode_natural_bound_cursor in Hdecode.
  destruct (decode_natural_cursor cursor) as [[decoded rest'] |]
    eqn:Hnatural; [| discriminate].
  destruct (decoded <=? max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_natural_cursor_some_positive.
  exact Hnatural.
Qed.

Lemma decode_backref_cursor_child_lt :
  forall index cursor child rest,
    decode_backref_cursor index cursor = Some (child, rest) ->
    child < index.
Proof.
  intros index cursor child rest Hdecode.
  unfold decode_backref_cursor in Hdecode.
  destruct (decode_natural_bound_cursor (Some index) cursor)
    as [[offset rest'] |] eqn:Hoffset; [| discriminate].
  pose proof
    (@decode_natural_bound_cursor_some index cursor offset rest' Hoffset)
    as Hoffset_le.
  pose proof
    (@decode_natural_bound_cursor_some_positive
      index cursor offset rest' Hoffset)
    as Hoffset_positive.
  inversion Hdecode; subst.
  lia.
Qed.

Lemma decode_raw_node_cursor_no_fail :
  forall index cursor node rest,
    decode_raw_node_cursor index cursor = Some (node, rest) ->
    raw_node_no_fail node = true.
Proof.
  intros index cursor node rest Hdecode.
  unfold decode_raw_node_cursor, decode_binary_node_cursor,
    decode_unary_node_cursor, decode_nullary_or_disconnect1_cursor in Hdecode.
  repeat match goal with
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
  end;
    try discriminate;
    inversion Hdecode; subst; reflexivity.
Qed.

Lemma decode_raw_node_cursor_no_disconnect1 :
  forall index cursor node rest,
    decode_raw_node_cursor index cursor = Some (node, rest) ->
    raw_node_no_disconnect1 node = true.
Proof.
  intros index cursor node rest Hdecode.
  unfold decode_raw_node_cursor, decode_binary_node_cursor,
    decode_unary_node_cursor, decode_nullary_or_disconnect1_cursor in Hdecode.
  repeat match goal with
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
  end;
    try discriminate;
    inversion Hdecode; subst; reflexivity.
Qed.

Theorem decode_raw_node_cursor_hidden_cmrs_256 :
  forall index cursor node rest,
    decode_raw_node_cursor index cursor = Some (node, rest) ->
    Forall cmr_bits_length_256 (raw_node_hidden_cmrs node).
Proof.
  intros index cursor node rest Hdecode.
  unfold decode_raw_node_cursor, decode_binary_node_cursor,
    decode_unary_node_cursor, decode_nullary_or_disconnect1_cursor in Hdecode.
  repeat match goal with
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
  end;
    try discriminate;
    inversion Hdecode; subst; simpl; try solve [constructor].
  constructor.
  - match goal with
    | H : read_hash256_cursor _ = Some (_, _) |- _ =>
        unfold cmr_bits_length_256;
        unfold read_hash256_cursor in H;
        eapply read_bits_cursor_length;
        exact H
    end.
  - constructor.
Qed.

Lemma decode_binary_node_cursor_children_before :
  forall index subcode cursor node rest,
    decode_binary_node_cursor index subcode cursor = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index subcode cursor node rest Hdecode child Hchild.
  unfold decode_binary_node_cursor in Hdecode.
  destruct (decode_backref_cursor index cursor)
    as [[lhs cursor'] |] eqn:Hlhs; [| discriminate].
  destruct (decode_backref_cursor index cursor')
    as [[rhs rest'] |] eqn:Hrhs; [| discriminate].
  destruct subcode as [| [| [| [| subcode']]]]; try discriminate.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_cursor_child_lt. exact Hlhs.
    + eapply decode_backref_cursor_child_lt. exact Hrhs.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_cursor_child_lt. exact Hlhs.
    + eapply decode_backref_cursor_child_lt. exact Hrhs.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_cursor_child_lt. exact Hlhs.
    + eapply decode_backref_cursor_child_lt. exact Hrhs.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_cursor_child_lt. exact Hlhs.
    + eapply decode_backref_cursor_child_lt. exact Hrhs.
Qed.

Lemma decode_unary_node_cursor_children_before :
  forall index subcode cursor node rest,
    decode_unary_node_cursor index subcode cursor = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index subcode cursor node rest Hdecode child Hchild.
  unfold decode_unary_node_cursor in Hdecode.
  destruct (decode_backref_cursor index cursor)
    as [[decoded_child rest'] |] eqn:Hdecoded_child; [| discriminate].
  destruct subcode as [| [| [| [| subcode']]]]; try discriminate.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_cursor_child_lt. exact Hdecoded_child.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_cursor_child_lt. exact Hdecoded_child.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_cursor_child_lt. exact Hdecoded_child.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_cursor_child_lt. exact Hdecoded_child.
Qed.

Lemma decode_nullary_or_disconnect1_cursor_children_before :
  forall index subcode cursor node rest,
    decode_nullary_or_disconnect1_cursor index subcode cursor =
      Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index subcode cursor node rest Hdecode child Hchild.
  unfold decode_nullary_or_disconnect1_cursor in Hdecode.
  destruct subcode as [| [| [| [| subcode']]]]; try discriminate.
  - inversion Hdecode; subst. cbn in Hchild. contradiction.
  - inversion Hdecode; subst. cbn in Hchild. contradiction.
Qed.

Theorem decode_raw_node_cursor_children_before :
  forall index cursor node rest,
    decode_raw_node_cursor index cursor = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index cursor node rest Hdecode.
  unfold decode_raw_node_cursor in Hdecode.
  destruct (read_bit_cursor cursor) as [[first_bit cursor'] |]
    eqn:Hfirst; [| discriminate].
  destruct first_bit.
  - destruct (read_bit_cursor cursor') as [[second_bit cursor''] |]
      eqn:Hsecond; [| discriminate].
    destruct second_bit.
    + destruct (decode_elements_jet_cursor cursor'')
        as [[jet rest'] |] eqn:Hjet; [| discriminate].
      inversion Hdecode; subst.
      intros child Hchild. simpl in Hchild. contradiction.
    + destruct (decode_natural_bound_cursor (Some 32) cursor'')
        as [[encoded_width cursor_after_width] |] eqn:Hwidth;
        [| discriminate].
      destruct (read_word_cursor encoded_width cursor_after_width)
        as [[value_bits rest'] |] eqn:Hword;
        [| discriminate].
      inversion Hdecode; subst.
      intros child Hchild. simpl in Hchild. contradiction.
  - destruct (read_u2_cursor cursor') as [[code cursor''] |] eqn:Hcode;
      [| discriminate].
    destruct code as [| [| [| [| code']]]].
    + destruct (read_u2_cursor cursor'') as [[subcode rest'] |]
        eqn:Hsubcode; [| discriminate].
      eapply decode_binary_node_cursor_children_before.
      exact Hdecode.
    + destruct (read_u2_cursor cursor'') as [[subcode rest'] |]
        eqn:Hsubcode; [| discriminate].
      eapply decode_unary_node_cursor_children_before.
      exact Hdecode.
    + destruct (read_u2_cursor cursor'') as [[subcode rest'] |]
        eqn:Hsubcode; [| discriminate].
      eapply decode_nullary_or_disconnect1_cursor_children_before.
      exact Hdecode.
    + destruct (read_bit_cursor cursor'') as [[witness_bit rest'] |]
        eqn:Hwitness; [| discriminate].
      destruct witness_bit.
      * inversion Hdecode; subst.
        intros child Hchild. simpl in Hchild. contradiction.
      * destruct (read_hash256_cursor rest')
          as [[cmr rest_after_hash] |] eqn:Hhash; [| discriminate].
        inversion Hdecode; subst.
        intros child Hchild. simpl in Hchild. contradiction.
    + discriminate.
Qed.
