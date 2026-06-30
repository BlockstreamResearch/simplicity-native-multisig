From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderRawOrder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition convert_raw_node
    (converted : list ConvertedNode)
    (seen_hidden : list (list bool))
    (raw : RawNode) : option (ConvertedNode * list (list bool)) :=
  let require_node index cont :=
      match get_converted_node converted index with
      | Some _ => Some (CNode (cont index), seen_hidden)
      | None => None
      end in
  let require_two_nodes lhs rhs cont :=
      match get_converted_node converted lhs, get_converted_node converted rhs with
      | Some _, Some _ => Some (CNode (cont lhs rhs), seen_hidden)
      | _, _ => None
      end in
  match raw with
  | RIden => Some (CNode SIden, seen_hidden)
  | RUnit => Some (CNode SUnit, seen_hidden)
  | RInjL child => require_node child SInjL
  | RInjR child => require_node child SInjR
  | RTake child => require_node child STake
  | RDrop child => require_node child SDrop
  | RComp lhs rhs => require_two_nodes lhs rhs SComp
  | RCase lhs rhs =>
      match nth_error converted lhs, nth_error converted rhs with
      | Some (CNode _), Some (CNode _) =>
          Some (CNode (SCase lhs rhs), seen_hidden)
      | Some (CNode _), Some (CHidden cmr_bits) =>
          Some (CNode (SAssertL lhs cmr_bits), seen_hidden)
      | Some (CHidden cmr_bits), Some (CNode _) =>
          Some (CNode (SAssertR cmr_bits rhs), seen_hidden)
      | Some (CHidden _), Some (CHidden _) => None
      | _, _ => None
      end
  | RPair lhs rhs => require_two_nodes lhs rhs SPair
  | RDisconnect1 lhs => require_node lhs SDisconnect1
  | RDisconnect lhs rhs => require_two_nodes lhs rhs SDisconnect
  | RWitness => Some (CNode SWitness, seen_hidden)
  | RFail entropy_bits => Some (CNode (SFail entropy_bits), seen_hidden)
  | RHidden cmr_bits =>
      if hidden_seen cmr_bits seen_hidden then None
      else Some (CHidden cmr_bits, cmr_bits :: seen_hidden)
  | RJet jet => Some (CNode (SJet jet), seen_hidden)
  | RWord encoded_width value_bits =>
      Some (CNode (SWord encoded_width value_bits), seen_hidden)
  end.

Fixpoint convert_raw_nodes
    (raw : list RawNode)
    (converted : list ConvertedNode)
    (seen_hidden : list (list bool)) :
    option (list ConvertedNode * list (list bool)) :=
  match raw with
  | [] => Some (converted, seen_hidden)
  | node :: rest =>
      match convert_raw_node converted seen_hidden node with
      | None => None
      | Some (converted_node, seen_hidden') =>
          convert_raw_nodes rest (converted ++ [converted_node]) seen_hidden'
      end
  end.
