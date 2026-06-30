From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderCursorProgramProofs.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition CmrBits := list bool.

Definition zero_hash256_bits : CmrBits := repeat false 256.

Definition cmr_bits_well_formed (cmr_bits : CmrBits) : bool :=
  Nat.eqb (length cmr_bits) 256.

Definition require_cmr_bits (cmr_bits : CmrBits) : option CmrBits :=
  if cmr_bits_well_formed cmr_bits then Some cmr_bits else None.

Record CmrAlgebra := {
  cmr_iden : CmrBits;
  cmr_unit : CmrBits;
  cmr_injl : CmrBits -> CmrBits;
  cmr_injr : CmrBits -> CmrBits;
  cmr_take : CmrBits -> CmrBits;
  cmr_drop : CmrBits -> CmrBits;
  cmr_comp : CmrBits -> CmrBits -> CmrBits;
  cmr_case : CmrBits -> CmrBits -> CmrBits;
  cmr_pair : CmrBits -> CmrBits -> CmrBits;
  cmr_disconnect : CmrBits -> CmrBits;
  cmr_witness : CmrBits;
  cmr_fail : list bool -> CmrBits;
  cmr_jet : ElementsJet -> CmrBits;
  cmr_word : nat -> list bool -> CmrBits
}.

Definition compute_structural_node_cmr
    (alg : CmrAlgebra)
    (computed : list CmrBits)
    (node : StructuralNode) : option CmrBits :=
  match node with
  | SIden => Some (cmr_iden alg)
  | SUnit => Some (cmr_unit alg)
  | SInjL child =>
      match nth_error computed child with
      | Some child_cmr => Some (cmr_injl alg child_cmr)
      | None => None
      end
  | SInjR child =>
      match nth_error computed child with
      | Some child_cmr => Some (cmr_injr alg child_cmr)
      | None => None
      end
  | STake child =>
      match nth_error computed child with
      | Some child_cmr => Some (cmr_take alg child_cmr)
      | None => None
      end
  | SDrop child =>
      match nth_error computed child with
      | Some child_cmr => Some (cmr_drop alg child_cmr)
      | None => None
      end
  | SComp lhs rhs =>
      match nth_error computed lhs, nth_error computed rhs with
      | Some lhs_cmr, Some rhs_cmr => Some (cmr_comp alg lhs_cmr rhs_cmr)
      | _, _ => None
      end
  | SCase lhs rhs =>
      match nth_error computed lhs, nth_error computed rhs with
      | Some lhs_cmr, Some rhs_cmr => Some (cmr_case alg lhs_cmr rhs_cmr)
      | _, _ => None
      end
  | SAssertL lhs hidden_cmr =>
      match nth_error computed lhs with
      | Some lhs_cmr => Some (cmr_case alg lhs_cmr hidden_cmr)
      | None => None
      end
  | SAssertR hidden_cmr rhs =>
      match nth_error computed rhs with
      | Some rhs_cmr => Some (cmr_case alg hidden_cmr rhs_cmr)
      | None => None
      end
  | SPair lhs rhs =>
      match nth_error computed lhs, nth_error computed rhs with
      | Some lhs_cmr, Some rhs_cmr => Some (cmr_pair alg lhs_cmr rhs_cmr)
      | _, _ => None
      end
  | SDisconnect1 lhs =>
      match nth_error computed lhs with
      | Some lhs_cmr => Some (cmr_disconnect alg lhs_cmr)
      | None => None
      end
  | SDisconnect lhs rhs =>
      match nth_error computed lhs, nth_error computed rhs with
      | Some lhs_cmr, Some _ => Some (cmr_disconnect alg lhs_cmr)
      | _, _ => None
      end
  | SWitness => Some (cmr_witness alg)
  | SFail entropy_bits => Some (cmr_fail alg entropy_bits)
  | SJet jet => Some (cmr_jet alg jet)
  | SWord encoded_width value_bits =>
      Some (cmr_word alg encoded_width value_bits)
  end.

Definition compute_converted_node_cmr
    (alg : CmrAlgebra)
    (computed : list CmrBits)
    (node : ConvertedNode) : option CmrBits :=
  match node with
  | CNode structural => compute_structural_node_cmr alg computed structural
  | CHidden hidden_cmr => Some hidden_cmr
  end.

Fixpoint compute_cmr_nodes
    (alg : CmrAlgebra)
    (nodes : list ConvertedNode)
    (computed : list CmrBits) : option (list CmrBits) :=
  match nodes with
  | [] => Some computed
  | node :: rest =>
      match compute_converted_node_cmr alg computed node with
      | None => None
      | Some node_cmr =>
          compute_cmr_nodes alg rest (computed ++ [node_cmr])
      end
  end.

Definition compute_structural_program_cmr
    (alg : CmrAlgebra)
    (program : StructuralProgram) : option CmrBits :=
  match compute_cmr_nodes alg (structural_nodes program) [] with
  | Some computed => nth_error computed (structural_root program)
  | None => None
  end.

Definition verify_structural_program_cmr
    (alg : CmrAlgebra)
    (program : StructuralProgram)
    (expected_cmr : CmrBits) : bool :=
  match compute_structural_program_cmr alg program with
  | Some actual_cmr => bits_eqb actual_cmr expected_cmr
  | None => false
  end.

Definition decode_structural_program_bytes_with_cmr
    (alg : CmrAlgebra)
    (bytes : list byte)
    (expected_cmr : CmrBits) : option StructuralProgram :=
  match decode_structural_program_bytes bytes with
  | Some program =>
      if verify_structural_program_cmr alg program expected_cmr
      then Some program
      else None
  | None => None
  end.

Definition decode_structural_program_bytes_streaming_with_cmr
    (alg : CmrAlgebra)
    (bytes : list byte)
    (expected_cmr : CmrBits) : option StructuralProgram :=
  match decode_structural_program_bytes_streaming bytes with
  | Some program =>
      if verify_structural_program_cmr alg program expected_cmr
      then Some program
      else None
  | None => None
  end.

Fixpoint compute_cmr_nodes_checked
    (alg : CmrAlgebra)
    (nodes : list ConvertedNode)
    (computed : list CmrBits) : option (list CmrBits) :=
  match nodes with
  | [] => Some computed
  | node :: rest =>
      match compute_converted_node_cmr alg computed node with
      | None => None
      | Some node_cmr =>
          match require_cmr_bits node_cmr with
          | None => None
          | Some checked_cmr =>
              compute_cmr_nodes_checked alg rest (computed ++ [checked_cmr])
          end
      end
  end.

Definition compute_structural_program_cmr_checked
    (alg : CmrAlgebra)
    (program : StructuralProgram) : option CmrBits :=
  match compute_cmr_nodes_checked alg (structural_nodes program) [] with
  | Some computed => nth_error computed (structural_root program)
  | None => None
  end.

Definition verify_structural_program_cmr_checked
    (alg : CmrAlgebra)
    (program : StructuralProgram)
    (expected_cmr : CmrBits) : bool :=
  match require_cmr_bits expected_cmr with
  | None => false
  | Some checked_expected =>
      match compute_structural_program_cmr_checked alg program with
      | Some actual_cmr => bits_eqb actual_cmr checked_expected
      | None => false
      end
  end.

Definition decode_structural_program_bytes_with_checked_cmr
    (alg : CmrAlgebra)
    (bytes : list byte)
    (expected_cmr : CmrBits) : option StructuralProgram :=
  match decode_structural_program_bytes bytes with
  | Some program =>
      if verify_structural_program_cmr_checked alg program expected_cmr
      then Some program
      else None
  | None => None
  end.

Definition decode_structural_program_bytes_streaming_with_checked_cmr
    (alg : CmrAlgebra)
    (bytes : list byte)
    (expected_cmr : CmrBits) : option StructuralProgram :=
  match decode_structural_program_bytes_streaming bytes with
  | Some program =>
      if verify_structural_program_cmr_checked alg program expected_cmr
      then Some program
      else None
  | None => None
  end.
