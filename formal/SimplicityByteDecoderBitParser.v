From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderValidation.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition decode_binary_node
    (index subcode : nat)
    (bits : list bool) : option (RawNode * list bool) :=
  match decode_backref index bits with
  | None => None
  | Some (lhs, bits') =>
      match decode_backref index bits' with
      | None => None
      | Some (rhs, rest) =>
          match subcode with
          | 0 => Some (RComp lhs rhs, rest)
          | 1 => Some (RCase lhs rhs, rest)
          | 2 => Some (RPair lhs rhs, rest)
          | 3 => Some (RDisconnect lhs rhs, rest)
          | _ => None
          end
      end
  end.

Definition decode_unary_node
    (index subcode : nat)
    (bits : list bool) : option (RawNode * list bool) :=
  match decode_backref index bits with
  | None => None
  | Some (child, rest) =>
      match subcode with
      | 0 => Some (RInjL child, rest)
      | 1 => Some (RInjR child, rest)
      | 2 => Some (RTake child, rest)
      | 3 => Some (RDrop child, rest)
      | _ => None
      end
  end.

Definition decode_nullary_or_disconnect1
    (index subcode : nat)
    (bits : list bool) : option (RawNode * list bool) :=
  match subcode with
  | 0 => Some (RIden, bits)
  | 1 => Some (RUnit, bits)
  | 2 => None
  | 3 => None
  | _ => None
  end.

Definition decode_raw_node (index : nat) (bits : list bool) :
    option (RawNode * list bool) :=
  match read_bit bits with
  | None => None
  | Some (true, bits') =>
      match read_bit bits' with
      | None => None
      | Some (true, bits'') =>
          match decode_elements_jet bits'' with
          | None => None
          | Some (jet, rest) => Some (RJet jet, rest)
          end
      | Some (false, bits'') =>
          match decode_natural_bound (Some 32) bits'' with
          | None => None
          | Some (encoded_width, bits''') =>
              match read_word encoded_width bits''' with
              | None => None
              | Some (value_bits, rest) =>
                  Some (RWord encoded_width value_bits, rest)
              end
          end
      end
  | Some (false, bits') =>
      match read_u2 bits' with
      | None => None
      | Some (code, bits'') =>
          match code with
          | 0 =>
              match read_u2 bits'' with
              | None => None
              | Some (subcode, rest) =>
                  decode_binary_node index subcode rest
              end
          | 1 =>
              match read_u2 bits'' with
              | None => None
              | Some (subcode, rest) =>
                  decode_unary_node index subcode rest
              end
          | 2 =>
              match read_u2 bits'' with
              | None => None
              | Some (subcode, rest) =>
                  decode_nullary_or_disconnect1 index subcode rest
              end
          | 3 =>
              match read_bit bits'' with
              | None => None
              | Some (true, rest) => Some (RWitness, rest)
              | Some (false, rest) =>
                  match read_hash256 rest with
                  | None => None
                  | Some (cmr, rest') => Some (RHidden cmr, rest')
                  end
              end
          | _ => None
          end
      end
  end.

Theorem decode_raw_node_no_fail :
  forall index bits node rest,
    decode_raw_node index bits = Some (node, rest) ->
    raw_node_no_fail node = true.
Proof.
  intros index bits node rest Hdecode.
  unfold decode_raw_node, decode_binary_node, decode_unary_node,
    decode_nullary_or_disconnect1 in Hdecode.
  repeat match goal with
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
  end;
    try discriminate;
    inversion Hdecode; subst; reflexivity.
Qed.

Theorem decode_raw_node_no_disconnect1 :
  forall index bits node rest,
    decode_raw_node index bits = Some (node, rest) ->
    raw_node_no_disconnect1 node = true.
Proof.
  intros index bits node rest Hdecode.
  unfold decode_raw_node, decode_binary_node, decode_unary_node,
    decode_nullary_or_disconnect1 in Hdecode.
  repeat match goal with
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
  end;
    try discriminate;
    inversion Hdecode; subst; reflexivity.
Qed.

Theorem decode_raw_node_hidden_cmrs_256 :
  forall index bits node rest,
    decode_raw_node index bits = Some (node, rest) ->
    Forall cmr_bits_length_256 (raw_node_hidden_cmrs node).
Proof.
  intros index bits node rest Hdecode.
  unfold decode_raw_node, decode_binary_node, decode_unary_node,
    decode_nullary_or_disconnect1 in Hdecode.
  repeat match goal with
  | H : context[match ?x with _ => _ end] |- _ =>
      destruct x eqn:?
  end;
    try discriminate;
    inversion Hdecode; subst; simpl; try solve [constructor].
  constructor.
  - match goal with
    | H : read_hash256 _ = Some (_, _) |- _ =>
        unfold cmr_bits_length_256;
        unfold read_hash256 in H;
        eapply read_bits_length;
        exact H
    end.
  - constructor.
Qed.

Definition raw_node_children_before (index : nat) (raw : RawNode) : Prop :=
  forall child,
    In child (raw_children raw) ->
    child < index.

Lemma decode_binary_node_children_before :
  forall index subcode bits node rest,
    decode_binary_node index subcode bits = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index subcode bits node rest Hdecode child Hchild.
  unfold decode_binary_node in Hdecode.
  destruct (decode_backref index bits) as [[lhs bits'] |] eqn:Hlhs;
    [| discriminate].
  destruct (decode_backref index bits') as [[rhs rest'] |] eqn:Hrhs;
    [| discriminate].
  destruct subcode as [| [| [| [| subcode']]]]; try discriminate.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_child_lt. exact Hlhs.
    + eapply decode_backref_child_lt. exact Hrhs.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_child_lt. exact Hlhs.
    + eapply decode_backref_child_lt. exact Hrhs.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_child_lt. exact Hlhs.
    + eapply decode_backref_child_lt. exact Hrhs.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | [Hchild | []]]; subst.
    + eapply decode_backref_child_lt. exact Hlhs.
    + eapply decode_backref_child_lt. exact Hrhs.
Qed.

Lemma decode_unary_node_children_before :
  forall index subcode bits node rest,
    decode_unary_node index subcode bits = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index subcode bits node rest Hdecode child Hchild.
  unfold decode_unary_node in Hdecode.
  destruct (decode_backref index bits) as [[decoded_child rest'] |]
    eqn:Hdecoded_child; [| discriminate].
  destruct subcode as [| [| [| [| subcode']]]]; try discriminate.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_child_lt. exact Hdecoded_child.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_child_lt. exact Hdecoded_child.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_child_lt. exact Hdecoded_child.
  - inversion Hdecode; subst.
    cbn in Hchild.
    destruct Hchild as [Hchild | []]; subst.
    eapply decode_backref_child_lt. exact Hdecoded_child.
Qed.

Lemma decode_nullary_or_disconnect1_children_before :
  forall index subcode bits node rest,
    decode_nullary_or_disconnect1 index subcode bits = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index subcode bits node rest Hdecode child Hchild.
  unfold decode_nullary_or_disconnect1 in Hdecode.
  destruct subcode as [| [| [| [| subcode']]]]; try discriminate.
  - inversion Hdecode; subst. cbn in Hchild. contradiction.
  - inversion Hdecode; subst. cbn in Hchild. contradiction.
Qed.

Theorem decode_raw_node_children_before :
  forall index bits node rest,
    decode_raw_node index bits = Some (node, rest) ->
    raw_node_children_before index node.
Proof.
  intros index bits node rest Hdecode.
  unfold decode_raw_node in Hdecode.
  destruct (read_bit bits) as [[first_bit bits'] |] eqn:Hfirst;
    [| discriminate].
  destruct first_bit.
  - destruct (read_bit bits') as [[second_bit bits''] |] eqn:Hsecond;
      [| discriminate].
    destruct second_bit.
    + destruct (decode_elements_jet bits'') as [[jet rest'] |] eqn:Hjet;
        [| discriminate].
      inversion Hdecode; subst.
      intros child Hchild. simpl in Hchild. contradiction.
    + destruct (decode_natural_bound (Some 32) bits'')
        as [[encoded_width bits_after_width] |] eqn:Hwidth;
        [| discriminate].
      destruct (read_word encoded_width bits_after_width)
        as [[value_bits rest'] |] eqn:Hword;
        [| discriminate].
      inversion Hdecode; subst.
      intros child Hchild. simpl in Hchild. contradiction.
  - destruct (read_u2 bits') as [[code bits''] |] eqn:Hcode;
      [| discriminate].
    destruct code as [| [| [| [| code']]]].
    + destruct (read_u2 bits'') as [[subcode rest'] |] eqn:Hsubcode;
        [| discriminate].
      eapply decode_binary_node_children_before.
      exact Hdecode.
    + destruct (read_u2 bits'') as [[subcode rest'] |] eqn:Hsubcode;
        [| discriminate].
      eapply decode_unary_node_children_before.
      exact Hdecode.
    + destruct (read_u2 bits'') as [[subcode rest'] |] eqn:Hsubcode;
        [| discriminate].
      eapply decode_nullary_or_disconnect1_children_before.
      exact Hdecode.
    + destruct (read_bit bits'') as [[witness_bit rest'] |] eqn:Hwitness;
        [| discriminate].
      destruct witness_bit.
      * inversion Hdecode; subst.
        intros child Hchild. simpl in Hchild. contradiction.
      * destruct (read_hash256 rest') as [[cmr rest_after_hash] |] eqn:Hhash;
          [| discriminate].
        inversion Hdecode; subst.
        intros child Hchild. simpl in Hchild. contradiction.
    + discriminate.
Qed.

Definition raw_program_children_before_from
    (start : nat)
    (raw : list RawNode) : Prop :=
  forall offset node child,
    nth_error raw offset = Some node ->
    In child (raw_children node) ->
    child < start + offset.

Fixpoint decode_raw_nodes
    (count index : nat)
    (bits : list bool) : option (list RawNode * list bool) :=
  match count with
  | 0 => Some ([], bits)
  | S count' =>
      match decode_raw_node index bits with
      | None => None
      | Some (node, bits') =>
          match decode_raw_nodes count' (S index) bits' with
          | None => None
          | Some (nodes, rest) => Some (node :: nodes, rest)
          end
      end
  end.

Fixpoint all_false (bits : list bool) : bool :=
  match bits with
  | [] => true
  | bit :: rest => negb bit && all_false rest
  end.
