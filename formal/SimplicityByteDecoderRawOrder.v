From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderProgramTypes.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Fixpoint nat_seen (needle : nat) (haystack : list nat) : bool :=
  match haystack with
  | [] => false
  | x :: xs => Nat.eqb needle x || nat_seen needle xs
  end.

Fixpoint nat_list_eqb (lhs rhs : list nat) : bool :=
  match lhs, rhs with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && nat_list_eqb xs ys
  | _, _ => false
  end.

Definition raw_children (raw : RawNode) : list nat :=
  match raw with
  | RIden
  | RUnit
  | RWitness
  | RFail _
  | RHidden _
  | RJet _
  | RWord _ _ => []
  | RInjL child
  | RInjR child
  | RTake child
  | RDrop child
  | RDisconnect1 child => [child]
  | RComp lhs rhs
  | RCase lhs rhs
  | RPair lhs rhs
  | RDisconnect lhs rhs => [lhs; rhs]
  end.

Definition raw_node_hidden_cmrs (raw : RawNode) : list (list bool) :=
  match raw with
  | RHidden cmr_bits => [cmr_bits]
  | _ => []
  end.

Fixpoint raw_program_hidden_cmrs (raw : list RawNode) : list (list bool) :=
  match raw with
  | [] => []
  | node :: rest =>
      raw_node_hidden_cmrs node ++ raw_program_hidden_cmrs rest
  end.

Definition raw_program_hidden_cmrs_256 (raw : list RawNode) : Prop :=
  Forall cmr_bits_length_256 (raw_program_hidden_cmrs raw).

Fixpoint raw_postorder_visit
    (fuel : nat)
    (nodes : list RawNode)
    (index : nat)
    (seen : list nat) : option (list nat * list nat) :=
  if nat_seen index seen then Some ([], seen)
  else
    match fuel with
    | 0 => None
    | S fuel' =>
        match nth_error nodes index with
        | None => None
        | Some node =>
            match raw_postorder_visit_children
              fuel' nodes (raw_children node) (index :: seen) with
            | None => None
            | Some (child_order, seen') =>
                Some (child_order ++ [index], seen')
            end
        end
  end
with raw_postorder_visit_children
    (fuel : nat)
    (nodes : list RawNode)
    (children : list nat)
    (seen : list nat) : option (list nat * list nat) :=
  match children with
  | [] => Some ([], seen)
  | child :: rest =>
      match fuel with
      | 0 => None
      | S fuel' =>
          match raw_postorder_visit fuel' nodes child seen with
          | None => None
          | Some (child_order, seen') =>
              match raw_postorder_visit_children fuel' nodes rest seen' with
              | None => None
              | Some (rest_order, seen'') =>
                  Some (child_order ++ rest_order, seen'')
              end
          end
      end
  end.

Fixpoint raw_postorder_visit_acc
    (fuel : nat)
    (nodes : list RawNode)
    (index : nat)
    (seen : list nat)
    (order_rev : list nat) : option (list nat * list nat) :=
  if nat_seen index seen then Some (seen, order_rev)
  else
    match fuel with
    | 0 => None
    | S fuel' =>
        match nth_error nodes index with
        | None => None
        | Some node =>
            match raw_postorder_visit_children_acc
              fuel' nodes (raw_children node) (index :: seen) order_rev with
            | None => None
            | Some (seen', order_rev') =>
                Some (seen', index :: order_rev')
            end
        end
    end
with raw_postorder_visit_children_acc
    (fuel : nat)
    (nodes : list RawNode)
    (children : list nat)
    (seen : list nat)
    (order_rev : list nat) : option (list nat * list nat) :=
  match children with
  | [] => Some (seen, order_rev)
  | child :: rest =>
      match fuel with
      | 0 => None
      | S fuel' =>
          match raw_postorder_visit_acc fuel' nodes child seen order_rev with
          | None => None
          | Some (seen', order_rev') =>
              raw_postorder_visit_children_acc
                fuel' nodes rest seen' order_rev'
          end
      end
  end.

Definition raw_postorder (nodes : list RawNode) : option (list nat) :=
  match nodes with
  | [] => None
  | _ =>
      match raw_postorder_visit
        (S (length nodes)) nodes (pred (length nodes)) [] with
      | Some (order, _) => Some order
      | None => None
      end
  end.

Definition raw_postorder_rev (nodes : list RawNode) : option (list nat) :=
  match nodes with
  | [] => None
  | _ =>
      match raw_postorder_visit_acc
        (S (length nodes)) nodes (pred (length nodes)) [] [] with
      | Some (_, order_rev) => Some order_rev
      | None => None
      end
  end.

Fixpoint get_reachable (index : nat) (reachable : list bool) : bool :=
  match index, reachable with
  | 0, bit :: _ => bit
  | S index', _ :: rest => get_reachable index' rest
  | _, [] => false
  end.

Fixpoint set_reachable (index : nat) (reachable : list bool) : list bool :=
  match index, reachable with
  | 0, _ :: rest => true :: rest
  | S index', bit :: rest => bit :: set_reachable index' rest
  | _, [] => []
  end.

Fixpoint mark_reachable_children
    (children : list nat)
    (reachable : list bool) : list bool :=
  match children with
  | [] => reachable
  | child :: rest =>
      mark_reachable_children rest (set_reachable child reachable)
  end.

Fixpoint mark_reachable_from_root_rev
    (index : nat)
    (nodes_rev : list RawNode)
    (reachable : list bool) : list bool :=
  match nodes_rev with
  | [] => reachable
  | node :: rest =>
      let reachable' :=
        if get_reachable index reachable then
          mark_reachable_children (raw_children node) reachable
        else reachable in
      match index with
      | 0 => mark_reachable_from_root_rev 0 rest reachable'
      | S index' => mark_reachable_from_root_rev index' rest reachable'
      end
  end.

Definition raw_all_nodes_reachable_from_root (nodes : list RawNode) : bool :=
  match nodes with
  | [] => false
  | _ =>
      let root := pred (length nodes) in
      let reachable :=
        mark_reachable_from_root_rev
          root
          (rev nodes)
          (set_reachable root (repeat false (length nodes))) in
      forallb (fun bit => bit) reachable
  end.

Definition raw_canonical_order (nodes : list RawNode) : bool :=
  raw_all_nodes_reachable_from_root nodes.

Definition get_converted_node (converted : list ConvertedNode) (index : nat) :
    option StructuralNode :=
  match nth_error converted index with
  | Some (CNode node) => Some node
  | _ => None
  end.

Lemma get_converted_node_child_is_nodeb :
  forall converted index node,
    get_converted_node converted index = Some node ->
    converted_child_is_nodeb converted index = true.
Proof.
  intros converted index node Hget.
  unfold get_converted_node in Hget.
  unfold converted_child_is_nodeb.
  destruct (nth_error converted index) as [[structural_node | hidden] |];
    try discriminate.
  reflexivity.
Qed.

Lemma nth_error_cnode_child_is_nodeb :
  forall converted index node,
    nth_error converted index = Some (CNode node) ->
    converted_child_is_nodeb converted index = true.
Proof.
  intros converted index node Hnth.
  unfold converted_child_is_nodeb.
  rewrite Hnth.
  reflexivity.
Qed.

Lemma converted_child_is_nodeb_sound :
  forall prefix index,
    converted_child_is_nodeb prefix index = true ->
    exists child_node,
      nth_error prefix index = Some (CNode child_node).
Proof.
  intros prefix index Hchild.
  unfold converted_child_is_nodeb in Hchild.
  destruct (nth_error prefix index) as [[child_node | hidden_cmr] |];
    try discriminate.
  exists child_node. reflexivity.
Qed.

Lemma nth_error_some_length :
  forall (A : Type) (xs : list A) index value,
    nth_error xs index = Some value ->
    index < length xs.
Proof.
  intros A xs index value Hnth.
  apply nth_error_Some.
  rewrite Hnth.
  discriminate.
Qed.

Lemma nth_error_app_prefix :
  forall (A : Type) (prefix suffix : list A) index value,
    nth_error prefix index = Some value ->
    nth_error (prefix ++ suffix) index = Some value.
Proof.
  intros A prefix.
  induction prefix as [| x prefix IH];
    intros suffix index value Hnth; destruct index; simpl in *;
    try discriminate.
  - exact Hnth.
  - apply IH. exact Hnth.
Qed.
