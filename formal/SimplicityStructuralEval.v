(*
  SimplicityStructuralEval.v — G4 step 1: a self-contained, executable big-step
  evaluator for decoded StructuralPrograms.

  Values are the standard Simplicity value universe (unit, sums, products);
  words evaluate to balanced bit trees (MSB-first, high half left).  The
  evaluator is parameterized by a jet interpretation and a per-node witness
  assignment.  Three-way results separate semantic failure (assertion/jet
  failure, the on-chain "script fails" outcome) from structural stuckness
  (missing child, type-shape mismatch, missing witness, disconnect), which a
  well-formed checked program must never reach — and, for the deployed
  artifact, provably does not reach on the concrete runs in
  CompiledMultisigExecution.v.

  Recursion is fueled; every recursive call targets a child node, and the
  decoder's children-before-parents invariant makes child indices strictly
  smaller, so fuel (S root) is always sufficient.

  PROOF-STYLE CONSTRAINT (memory): no [Set Implicit Arguments]/[Set Strict
  Implicit] in files that touch the concrete artifact.
*)

From Coq Require Import List Bool Arith.
From MultisigFormal Require Import SimplicityByteDecoder ElementsJets.

Import ListNotations.

Inductive SValue :=
| VUnit
| VLeft (v : SValue)
| VRight (v : SValue)
| VPair (a b : SValue).

Inductive EvalResult :=
| EValue (v : SValue)
| EFail
| EStuck.

(* Simplicity booleans/bits: 0 = inl (), 1 = inr (). *)
Definition value_of_bit (b : bool) : SValue :=
  if b then VRight VUnit else VLeft VUnit.

(* A word of 2^log_width bits as a balanced tree, MSB-first, high half left. *)
Fixpoint value_of_bits (log_width : nat) (bits : list bool) : SValue :=
  match log_width with
  | 0 =>
      match bits with
      | b :: _ => value_of_bit b
      | [] => VLeft VUnit
      end
  | S log_width' =>
      let half := Nat.pow 2 log_width' in
      VPair
        (value_of_bits log_width' (firstn half bits))
        (value_of_bits log_width' (skipn half bits))
  end.

Fixpoint bits_of_value (log_width : nat) (v : SValue) :
    option (list bool) :=
  match log_width, v with
  | 0, VLeft VUnit => Some [false]
  | 0, VRight VUnit => Some [true]
  | S log_width', VPair hi lo =>
      match bits_of_value log_width' hi, bits_of_value log_width' lo with
      | Some hi_bits, Some lo_bits => Some (hi_bits ++ lo_bits)
      | _, _ => None
      end
  | _, _ => None
  end.

Section Eval.

Variable jet_sem : ElementsJet -> SValue -> EvalResult.
Variable witness_at : nat -> option SValue.
Variable nodes : list ConvertedNode.

Fixpoint eval_node (fuel index : nat) (input : SValue) : EvalResult :=
  match fuel with
  | 0 => EStuck
  | S fuel' =>
      match nth_error nodes index with
      | Some (CNode node) =>
          match node with
          | SIden => EValue input
          | SUnit => EValue VUnit
          | SInjL child =>
              match eval_node fuel' child input with
              | EValue v => EValue (VLeft v)
              | other => other
              end
          | SInjR child =>
              match eval_node fuel' child input with
              | EValue v => EValue (VRight v)
              | other => other
              end
          | STake child =>
              match input with
              | VPair a _ => eval_node fuel' child a
              | _ => EStuck
              end
          | SDrop child =>
              match input with
              | VPair _ b => eval_node fuel' child b
              | _ => EStuck
              end
          | SComp lhs rhs =>
              match eval_node fuel' lhs input with
              | EValue mid => eval_node fuel' rhs mid
              | other => other
              end
          | SCase lhs rhs =>
              match input with
              | VPair (VLeft a) c => eval_node fuel' lhs (VPair a c)
              | VPair (VRight b) c => eval_node fuel' rhs (VPair b c)
              | _ => EStuck
              end
          | SAssertL lhs _ =>
              match input with
              | VPair (VLeft a) c => eval_node fuel' lhs (VPair a c)
              | VPair (VRight _) _ => EFail
              | _ => EStuck
              end
          | SAssertR _ rhs =>
              match input with
              | VPair (VLeft _) _ => EFail
              | VPair (VRight b) c => eval_node fuel' rhs (VPair b c)
              | _ => EStuck
              end
          | SPair lhs rhs =>
              match eval_node fuel' lhs input with
              | EValue a =>
                  match eval_node fuel' rhs input with
                  | EValue b => EValue (VPair a b)
                  | other => other
                  end
              | other => other
              end
          | SWitness =>
              match witness_at index with
              | Some v => EValue v
              | None => EStuck
              end
          | SJet jet => jet_sem jet input
          | SWord encoded_width value_bits =>
              match encoded_width with
              | 0 => EStuck
              | S log_width => EValue (value_of_bits log_width value_bits)
              end
          | SFail _ => EFail
          | SDisconnect1 _ => EStuck
          | SDisconnect _ _ => EStuck
          end
      | Some (CHidden _) => EFail
      | None => EStuck
      end
  end.

End Eval.

(* Evaluate a whole program on an input value.  Fuel (S root) is sufficient
   because the decoder guarantees children strictly precede parents. *)
Definition eval_structural_program
    (jet_sem : ElementsJet -> SValue -> EvalResult)
    (witness_at : nat -> option SValue)
    (program : StructuralProgram)
    (input : SValue) : EvalResult :=
  eval_node
    jet_sem
    witness_at
    (structural_nodes program)
    (S (structural_root program))
    (structural_root program)
    input.
