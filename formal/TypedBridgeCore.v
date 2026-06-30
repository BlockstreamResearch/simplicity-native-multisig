From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import ElementsJets SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Typed bridge skeleton for decoded structural programs.

  This is not yet the final import into the Simplicity foundation's dependent
  Term type.  It is the checked certificate layer immediately before that: an
  exported type table must assign an arrow type to each real decoded node and
  no type to hidden CMR placeholders.  Core combinators are checked here; jets,
  witnesses, words, fails, and disconnect forms are delegated to explicit
  hooks so later work can instantiate them from the foundation/Elements
  primitive type tables.
*)

Inductive BridgeType :=
| BTUnit
| BTSum (left right : BridgeType)
| BTProd (left right : BridgeType)
| BTAtom (tag : nat).

Record BridgeArrow := {
  bridge_source : BridgeType;
  bridge_target : BridgeType
}.

Fixpoint bridge_type_atom_free (ty : BridgeType) : bool :=
  match ty with
  | BTUnit => true
  | BTSum ty_left ty_right
  | BTProd ty_left ty_right =>
      bridge_type_atom_free ty_left && bridge_type_atom_free ty_right
  | BTAtom _ => false
  end.

Definition bridge_arrow_atom_free (arrow : BridgeArrow) : bool :=
  bridge_type_atom_free (bridge_source arrow) &&
  bridge_type_atom_free (bridge_target arrow).

Definition option_bridge_arrow_atom_free
    (entry : option BridgeArrow) : bool :=
  match entry with
  | Some arrow => bridge_arrow_atom_free arrow
  | None => true
  end.

Fixpoint bridge_type_eqb (lhs rhs : BridgeType) : bool :=
  match lhs, rhs with
  | BTUnit, BTUnit => true
  | BTSum lhs_left lhs_right, BTSum rhs_left rhs_right
  | BTProd lhs_left lhs_right, BTProd rhs_left rhs_right =>
      bridge_type_eqb lhs_left rhs_left &&
      bridge_type_eqb lhs_right rhs_right
  | BTAtom lhs_tag, BTAtom rhs_tag => Nat.eqb lhs_tag rhs_tag
  | _, _ => false
  end.

Definition bridge_arrow_eqb (lhs rhs : BridgeArrow) : bool :=
  bridge_type_eqb (bridge_source lhs) (bridge_source rhs) &&
  bridge_type_eqb (bridge_target lhs) (bridge_target rhs).

Record TypeHooks := {
  hook_jet_arrow : ElementsJet -> BridgeArrow;
  hook_witness_allowed : BridgeArrow -> bool;
  hook_fail_allowed : list bool -> BridgeArrow -> bool;
  hook_word_allowed : nat -> list bool -> BridgeArrow -> bool;
  hook_disconnect1_allowed : BridgeArrow -> BridgeArrow -> bool;
  hook_disconnect_allowed : BridgeArrow -> BridgeArrow -> BridgeArrow -> bool
}.

Definition typed_prefix_lookup
    (prefix : list (option BridgeArrow))
    (index : nat) : option BridgeArrow :=
  match nth_error prefix index with
  | Some (Some arrow) => Some arrow
  | _ => None
  end.

Definition child_arrow_eqb
    (prefix : list (option BridgeArrow))
    (index : nat)
    (expected : BridgeArrow) : bool :=
  match typed_prefix_lookup prefix index with
  | Some actual => bridge_arrow_eqb actual expected
  | None => false
  end.

Definition typecheck_structural_node
    (hooks : TypeHooks)
    (prefix : list (option BridgeArrow))
    (node : StructuralNode)
    (arrow : BridgeArrow) : bool :=
  let source := bridge_source arrow in
  let target := bridge_target arrow in
  match node with
  | SIden => bridge_type_eqb source target
  | SUnit => bridge_type_eqb target BTUnit
  | SInjL child =>
      match target with
      | BTSum sum_left _ =>
          child_arrow_eqb prefix child
            {| bridge_source := source; bridge_target := sum_left |}
      | _ => false
      end
  | SInjR child =>
      match target with
      | BTSum _ sum_right =>
          child_arrow_eqb prefix child
            {| bridge_source := source; bridge_target := sum_right |}
      | _ => false
      end
  | STake child =>
      match source with
      | BTProd prod_left _ =>
          child_arrow_eqb prefix child
            {| bridge_source := prod_left; bridge_target := target |}
      | _ => false
      end
  | SDrop child =>
      match source with
      | BTProd _ prod_right =>
          child_arrow_eqb prefix child
            {| bridge_source := prod_right; bridge_target := target |}
      | _ => false
      end
  | SComp lhs rhs =>
      match typed_prefix_lookup prefix lhs, typed_prefix_lookup prefix rhs with
      | Some lhs_arrow, Some rhs_arrow =>
          bridge_type_eqb (bridge_source lhs_arrow) source &&
          bridge_type_eqb (bridge_target lhs_arrow) (bridge_source rhs_arrow) &&
          bridge_type_eqb (bridge_target rhs_arrow) target
      | _, _ => false
      end
  | SCase lhs rhs =>
      match source with
      | BTProd (BTSum sum_left sum_right) ctx =>
          child_arrow_eqb prefix lhs
            {| bridge_source := BTProd sum_left ctx; bridge_target := target |} &&
          child_arrow_eqb prefix rhs
            {| bridge_source := BTProd sum_right ctx; bridge_target := target |}
      | _ => false
      end
  | SAssertL lhs _ =>
      match source with
      | BTProd (BTSum sum_left _) ctx =>
          child_arrow_eqb prefix lhs
            {| bridge_source := BTProd sum_left ctx; bridge_target := target |}
      | _ => false
      end
  | SAssertR _ rhs =>
      match source with
      | BTProd (BTSum _ sum_right) ctx =>
          child_arrow_eqb prefix rhs
            {| bridge_source := BTProd sum_right ctx; bridge_target := target |}
      | _ => false
      end
  | SPair lhs rhs =>
      match target with
      | BTProd prod_left prod_right =>
          child_arrow_eqb prefix lhs
            {| bridge_source := source; bridge_target := prod_left |} &&
          child_arrow_eqb prefix rhs
            {| bridge_source := source; bridge_target := prod_right |}
      | _ => false
      end
  | SDisconnect1 lhs =>
      match typed_prefix_lookup prefix lhs with
      | Some lhs_arrow => hook_disconnect1_allowed hooks lhs_arrow arrow
      | None => false
      end
  | SDisconnect lhs rhs =>
      match typed_prefix_lookup prefix lhs, typed_prefix_lookup prefix rhs with
      | Some lhs_arrow, Some rhs_arrow =>
          hook_disconnect_allowed hooks lhs_arrow rhs_arrow arrow
      | _, _ => false
      end
  | SWitness => hook_witness_allowed hooks arrow
  | SFail entropy_bits => hook_fail_allowed hooks entropy_bits arrow
  | SJet jet => bridge_arrow_eqb (hook_jet_arrow hooks jet) arrow
  | SWord encoded_width value_bits =>
      hook_word_allowed hooks encoded_width value_bits arrow
  end.

Definition child_has_arrow
    (prefix : list (option BridgeArrow))
    (index : nat)
    (expected : BridgeArrow) : Prop :=
  typed_prefix_lookup prefix index = Some expected.

Definition structural_node_type_evidence
    (hooks : TypeHooks)
    (prefix : list (option BridgeArrow))
    (node : StructuralNode)
    (arrow : BridgeArrow) : Prop :=
  let source := bridge_source arrow in
  let target := bridge_target arrow in
  match node with
  | SIden =>
      source = target
  | SUnit =>
      target = BTUnit
  | SInjL child =>
      exists sum_left sum_right,
        target = BTSum sum_left sum_right /\
        child_has_arrow prefix child
          {| bridge_source := source; bridge_target := sum_left |}
  | SInjR child =>
      exists sum_left sum_right,
        target = BTSum sum_left sum_right /\
        child_has_arrow prefix child
          {| bridge_source := source; bridge_target := sum_right |}
  | STake child =>
      exists prod_left prod_right,
        source = BTProd prod_left prod_right /\
        child_has_arrow prefix child
          {| bridge_source := prod_left; bridge_target := target |}
  | SDrop child =>
      exists prod_left prod_right,
        source = BTProd prod_left prod_right /\
        child_has_arrow prefix child
          {| bridge_source := prod_right; bridge_target := target |}
  | SComp lhs rhs =>
      exists lhs_arrow rhs_arrow,
        typed_prefix_lookup prefix lhs = Some lhs_arrow /\
        typed_prefix_lookup prefix rhs = Some rhs_arrow /\
        bridge_source lhs_arrow = source /\
        bridge_target lhs_arrow = bridge_source rhs_arrow /\
        bridge_target rhs_arrow = target
  | SCase lhs rhs =>
      exists sum_left sum_right ctx,
        source = BTProd (BTSum sum_left sum_right) ctx /\
        child_has_arrow prefix lhs
          {| bridge_source := BTProd sum_left ctx; bridge_target := target |} /\
        child_has_arrow prefix rhs
          {| bridge_source := BTProd sum_right ctx; bridge_target := target |}
  | SAssertL lhs _ =>
      exists sum_left sum_right ctx,
        source = BTProd (BTSum sum_left sum_right) ctx /\
        child_has_arrow prefix lhs
          {| bridge_source := BTProd sum_left ctx; bridge_target := target |}
  | SAssertR _ rhs =>
      exists sum_left sum_right ctx,
        source = BTProd (BTSum sum_left sum_right) ctx /\
        child_has_arrow prefix rhs
          {| bridge_source := BTProd sum_right ctx; bridge_target := target |}
  | SPair lhs rhs =>
      exists prod_left prod_right,
        target = BTProd prod_left prod_right /\
        child_has_arrow prefix lhs
          {| bridge_source := source; bridge_target := prod_left |} /\
        child_has_arrow prefix rhs
          {| bridge_source := source; bridge_target := prod_right |}
  | SDisconnect1 lhs =>
      exists lhs_arrow,
        typed_prefix_lookup prefix lhs = Some lhs_arrow /\
        hook_disconnect1_allowed hooks lhs_arrow arrow = true
  | SDisconnect lhs rhs =>
      exists lhs_arrow rhs_arrow,
        typed_prefix_lookup prefix lhs = Some lhs_arrow /\
        typed_prefix_lookup prefix rhs = Some rhs_arrow /\
        hook_disconnect_allowed hooks lhs_arrow rhs_arrow arrow = true
  | SWitness =>
      hook_witness_allowed hooks arrow = true
  | SFail entropy_bits =>
      hook_fail_allowed hooks entropy_bits arrow = true
  | SJet jet =>
      hook_jet_arrow hooks jet = arrow
  | SWord encoded_width value_bits =>
      hook_word_allowed hooks encoded_width value_bits arrow = true
  end.

Fixpoint check_typed_nodes_from
    (hooks : TypeHooks)
    (prefix : list (option BridgeArrow))
    (nodes : list ConvertedNode)
    (types : list (option BridgeArrow)) : bool :=
  match nodes, types with
  | [], [] => true
  | CNode node :: rest_nodes, Some arrow :: rest_types =>
      typecheck_structural_node hooks prefix node arrow &&
      check_typed_nodes_from
        hooks
        (prefix ++ [Some arrow])
        rest_nodes
        rest_types
  | CHidden _ :: rest_nodes, None :: rest_types =>
      check_typed_nodes_from hooks (prefix ++ [None]) rest_nodes rest_types
  | _, _ => false
  end.

Definition typed_entry_matches_node
    (node : ConvertedNode)
    (entry : option BridgeArrow) : Prop :=
  match node, entry with
  | CNode _, Some _ => True
  | CHidden _, None => True
  | _, _ => False
  end.

Definition typed_table_matches_program
    (program : StructuralProgram)
    (types : list (option BridgeArrow)) : Prop :=
  Forall2 typed_entry_matches_node (structural_nodes program) types.

Fixpoint typed_nodes_type_evidence_from
    (hooks : TypeHooks)
    (prefix : list (option BridgeArrow))
    (nodes : list ConvertedNode)
    (types : list (option BridgeArrow)) : Prop :=
  match nodes, types with
  | [], [] => True
  | CNode node :: rest_nodes, Some arrow :: rest_types =>
      structural_node_type_evidence hooks prefix node arrow /\
      typed_nodes_type_evidence_from
        hooks
        (prefix ++ [Some arrow])
        rest_nodes
        rest_types
  | CHidden _ :: rest_nodes, None :: rest_types =>
      typed_nodes_type_evidence_from
        hooks
        (prefix ++ [None])
        rest_nodes
        rest_types
  | _, _ => False
  end.

Definition typed_program_nodes_have_type_evidence
    (hooks : TypeHooks)
    (program : StructuralProgram)
    (types : list (option BridgeArrow)) : Prop :=
  typed_nodes_type_evidence_from hooks [] (structural_nodes program) types.

Definition typed_program_child_references_have_arrows
    (program : StructuralProgram)
    (types : list (option BridgeArrow)) : Prop :=
  forall parent node child,
    nth_error (structural_nodes program) parent = Some (CNode node) ->
    In child (structural_node_children node) ->
    exists child_node child_arrow,
      nth_error (structural_nodes program) child = Some (CNode child_node) /\
      nth_error types child = Some (Some child_arrow) /\
      child < parent.

Definition typed_program_root_has_arrow
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : Prop :=
  exists root_node,
    nth_error (structural_nodes program) (structural_root program) =
      Some (CNode root_node) /\
    nth_error types (structural_root program) = Some (Some root_arrow).

Definition typed_root_entry
    (program : StructuralProgram)
    (types : list (option BridgeArrow)) : option BridgeArrow :=
  match nth_error types (structural_root program) with
  | Some (Some arrow) => Some arrow
  | _ => None
  end.

Definition check_typed_structural_program
    (hooks : TypeHooks)
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : bool :=
  check_typed_nodes_from hooks [] (structural_nodes program) types &&
  match typed_root_entry program types with
  | Some actual_root_arrow => bridge_arrow_eqb actual_root_arrow root_arrow
  | None => false
  end.

Record TypedStructuralProgramEvidence
    (hooks : TypeHooks)
    (program : StructuralProgram)
    (types : list (option BridgeArrow))
    (root_arrow : BridgeArrow) : Prop := {
  typed_nodes_checked :
    check_typed_nodes_from hooks [] (structural_nodes program) types = true;
  typed_node_type_evidence :
    typed_program_nodes_have_type_evidence hooks program types;
  typed_table_length :
    length (structural_nodes program) = length types;
  typed_table_shape :
    typed_table_matches_program program types;
  typed_root_checked :
    typed_root_entry program types = Some root_arrow
}.
