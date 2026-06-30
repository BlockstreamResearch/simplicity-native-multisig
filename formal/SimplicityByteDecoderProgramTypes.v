From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export ElementsJets SimplicityByteDecoderBits.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Inductive RawNode :=
| RIden
| RUnit
| RInjL (child : nat)
| RInjR (child : nat)
| RTake (child : nat)
| RDrop (child : nat)
| RComp (lhs rhs : nat)
| RCase (lhs rhs : nat)
| RPair (lhs rhs : nat)
| RDisconnect1 (lhs : nat)
| RDisconnect (lhs rhs : nat)
| RWitness
| RFail (entropy_bits : list bool)
| RHidden (cmr_bits : list bool)
| RJet (jet : ElementsJet)
| RWord (encoded_width : nat) (value_bits : list bool).

Inductive StructuralNode :=
| SIden
| SUnit
| SInjL (child : nat)
| SInjR (child : nat)
| STake (child : nat)
| SDrop (child : nat)
| SComp (lhs rhs : nat)
| SCase (lhs rhs : nat)
| SAssertL (lhs : nat) (hidden_cmr_bits : list bool)
| SAssertR (hidden_cmr_bits : list bool) (rhs : nat)
| SPair (lhs rhs : nat)
| SDisconnect1 (lhs : nat)
| SDisconnect (lhs rhs : nat)
| SWitness
| SFail (entropy_bits : list bool)
| SJet (jet : ElementsJet)
| SWord (encoded_width : nat) (value_bits : list bool).

Inductive ConvertedNode :=
| CNode (node : StructuralNode)
| CHidden (cmr_bits : list bool).

Record StructuralProgram := {
  structural_nodes : list ConvertedNode;
  structural_root : nat
}.

Definition structural_node_children (node : StructuralNode) : list nat :=
  match node with
  | SIden
  | SUnit
  | SWitness
  | SFail _
  | SJet _
  | SWord _ _ => []
  | SInjL child
  | SInjR child
  | STake child
  | SDrop child
  | SDisconnect1 child => [child]
  | SAssertL lhs _
  | SAssertR _ lhs => [lhs]
  | SComp lhs rhs
  | SCase lhs rhs
  | SPair lhs rhs
  | SDisconnect lhs rhs => [lhs; rhs]
  end.

Definition converted_child_is_nodeb
    (prefix : list ConvertedNode)
    (index : nat) : bool :=
  match nth_error prefix index with
  | Some (CNode _) => true
  | _ => false
  end.

Definition structural_node_backrefs_are_nodesb
    (prefix : list ConvertedNode)
    (node : StructuralNode) : bool :=
  forallb (converted_child_is_nodeb prefix) (structural_node_children node).

Definition converted_node_backrefs_are_nodesb
    (prefix : list ConvertedNode)
    (node : ConvertedNode) : bool :=
  match node with
  | CNode structural_node =>
      structural_node_backrefs_are_nodesb prefix structural_node
  | CHidden _ => true
  end.

Fixpoint converted_nodes_backrefs_are_nodesb_from
    (prefix nodes : list ConvertedNode) : bool :=
  match nodes with
  | [] => true
  | node :: rest =>
      converted_node_backrefs_are_nodesb prefix node &&
      converted_nodes_backrefs_are_nodesb_from (prefix ++ [node]) rest
  end.

Definition structural_program_dag_well_formed
    (program : StructuralProgram) : bool :=
  match nth_error (structural_nodes program) (structural_root program) with
  | Some (CNode _) =>
      converted_nodes_backrefs_are_nodesb_from [] (structural_nodes program)
  | _ => false
  end.

Definition structural_program_child_references_are_backward_nodes
    (program : StructuralProgram) : Prop :=
  forall parent node child,
    nth_error (structural_nodes program) parent = Some (CNode node) ->
    In child (structural_node_children node) ->
    exists child_node,
      nth_error (structural_nodes program) child = Some (CNode child_node) /\
      child < parent.

Definition structural_node_jets (node : StructuralNode) : list ElementsJet :=
  match node with
  | SJet jet => [jet]
  | _ => []
  end.

Definition converted_node_jets (node : ConvertedNode) : list ElementsJet :=
  match node with
  | CNode structural_node => structural_node_jets structural_node
  | CHidden _ => []
  end.

Definition structural_program_jets
    (program : StructuralProgram) : list ElementsJet :=
  concat (map converted_node_jets (structural_nodes program)).

Definition structural_program_uses_only_multisig_jets
    (program : StructuralProgram) : Prop :=
  Forall multisig_elements_jet (structural_program_jets program).

Lemma converted_node_jets_are_multisig_subset :
  forall node,
    Forall multisig_elements_jet (converted_node_jets node).
Proof.
  intros node.
  destruct node as [structural_node | hidden_cmr_bits].
  - destruct structural_node; simpl; try solve [constructor].
    constructor.
    + exact (elements_jet_is_multisig_elements_jet jet).
    + constructor.
  - simpl. constructor.
Qed.

Theorem structural_program_jets_are_multisig_subset :
  forall program,
    structural_program_uses_only_multisig_jets program.
Proof.
  intros program.
  unfold structural_program_uses_only_multisig_jets.
  unfold structural_program_jets.
  destruct program as [nodes root].
  induction nodes as [| node rest IH]; simpl.
  - constructor.
  - apply Forall_app. split.
    + apply converted_node_jets_are_multisig_subset.
    + exact IH.
Qed.

Definition raw_node_no_fail (raw : RawNode) : bool :=
  match raw with
  | RFail _ => false
  | _ => true
  end.

Definition raw_program_no_fail (raw : list RawNode) : bool :=
  forallb raw_node_no_fail raw.

Definition structural_node_no_fail (node : StructuralNode) : bool :=
  match node with
  | SFail _ => false
  | _ => true
  end.

Definition converted_node_no_fail (node : ConvertedNode) : bool :=
  match node with
  | CNode structural_node => structural_node_no_fail structural_node
  | CHidden _ => true
  end.

Definition structural_program_no_fail (program : StructuralProgram) : bool :=
  forallb converted_node_no_fail (structural_nodes program).

Theorem structural_program_no_fail_no_sfail_node :
  forall program index entropy_bits,
    structural_program_no_fail program = true ->
    nth_error (structural_nodes program) index =
      Some (CNode (SFail entropy_bits)) ->
    False.
Proof.
  intros program index entropy_bits Hno_fail Hnth.
  unfold structural_program_no_fail in Hno_fail.
  apply nth_error_In in Hnth.
  apply forallb_forall with (x := CNode (SFail entropy_bits)) in Hno_fail.
  - simpl in Hno_fail. discriminate.
  - exact Hnth.
Qed.

Definition raw_node_no_disconnect1 (raw : RawNode) : bool :=
  match raw with
  | RDisconnect1 _ => false
  | _ => true
  end.

Definition raw_program_no_disconnect1 (raw : list RawNode) : bool :=
  forallb raw_node_no_disconnect1 raw.

Definition structural_node_no_disconnect1 (node : StructuralNode) : bool :=
  match node with
  | SDisconnect1 _ => false
  | _ => true
  end.

Definition converted_node_no_disconnect1 (node : ConvertedNode) : bool :=
  match node with
  | CNode structural_node => structural_node_no_disconnect1 structural_node
  | CHidden _ => true
  end.

Definition structural_program_no_disconnect1
    (program : StructuralProgram) : bool :=
  forallb converted_node_no_disconnect1 (structural_nodes program).

Theorem structural_program_no_disconnect1_no_sdisconnect1_node :
  forall program index child,
    structural_program_no_disconnect1 program = true ->
    nth_error (structural_nodes program) index =
      Some (CNode (SDisconnect1 child)) ->
    False.
Proof.
  intros program index child Hno_disconnect1 Hnth.
  unfold structural_program_no_disconnect1 in Hno_disconnect1.
  apply nth_error_In in Hnth.
  apply forallb_forall with (x := CNode (SDisconnect1 child))
    in Hno_disconnect1.
  - simpl in Hno_disconnect1. discriminate.
  - exact Hnth.
Qed.

Definition converted_node_hidden_cmrs (node : ConvertedNode) : list (list bool) :=
  match node with
  | CNode _ => []
  | CHidden cmr_bits => [cmr_bits]
  end.

Fixpoint converted_nodes_hidden_cmrs
    (nodes : list ConvertedNode) : list (list bool) :=
  match nodes with
  | [] => []
  | node :: rest =>
      converted_node_hidden_cmrs node ++ converted_nodes_hidden_cmrs rest
  end.

Definition structural_program_hidden_cmrs (program : StructuralProgram) :
    list (list bool) :=
  converted_nodes_hidden_cmrs (structural_nodes program).

Definition structural_program_hidden_cmrs_unique
    (program : StructuralProgram) : Prop :=
  NoDup (structural_program_hidden_cmrs program).

Definition cmr_bits_length_256 (cmr_bits : list bool) : Prop :=
  length cmr_bits = 256.

Definition structural_program_hidden_cmrs_256
    (program : StructuralProgram) : Prop :=
  Forall cmr_bits_length_256 (structural_program_hidden_cmrs program).

Fixpoint bits_eqb (a b : list bool) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Bool.eqb x y && bits_eqb xs ys
  | _, _ => false
  end.

Lemma bits_eqb_refl :
  forall bits,
    bits_eqb bits bits = true.
Proof.
  induction bits as [| bit rest IH]; simpl.
  - reflexivity.
  - destruct bit; simpl; exact IH.
Qed.

Fixpoint hidden_seen (cmr_bits : list bool) (seen : list (list bool)) : bool :=
  match seen with
  | [] => false
  | cmr_bits' :: seen' =>
      bits_eqb cmr_bits cmr_bits' || hidden_seen cmr_bits seen'
  end.

Lemma hidden_seen_in :
  forall cmr_bits seen,
    In cmr_bits seen ->
    hidden_seen cmr_bits seen = true.
Proof.
  intros cmr_bits seen.
  induction seen as [| seen_head seen_tail IH];
    intros Hin; simpl in Hin; [contradiction |].
  destruct Hin as [Heq | Hin_tail].
  - subst seen_head.
    simpl.
    rewrite bits_eqb_refl.
    reflexivity.
  - simpl.
    destruct (bits_eqb cmr_bits seen_head); [reflexivity |].
    apply IH. exact Hin_tail.
Qed.

Lemma hidden_seen_false_not_in :
  forall cmr_bits seen,
    hidden_seen cmr_bits seen = false ->
    ~ In cmr_bits seen.
Proof.
  intros cmr_bits seen Hseen Hin.
  rewrite (@hidden_seen_in cmr_bits seen Hin) in Hseen.
  discriminate.
Qed.
