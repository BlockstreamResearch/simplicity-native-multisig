From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderBitParser.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Record BitCursor := {
  cursor_bytes : list byte;
  cursor_offset : nat
}.

Definition cursor_start (bytes : list byte) : BitCursor :=
  {| cursor_bytes := bytes; cursor_offset := 0 |}.

Definition bit_at_offset (b offset : nat) : bool :=
  Nat.odd ((b / Nat.pow 2 (7 - offset)) mod 2).

Definition read_bit_cursor (cursor : BitCursor) :
    option (bool * BitCursor) :=
  match cursor_bytes cursor with
  | [] => None
  | byte :: rest =>
      if cursor_offset cursor <? 8 then
        let bit := bit_at_offset byte (cursor_offset cursor) in
        let next_cursor :=
          if Nat.eqb (cursor_offset cursor) 7 then
            {| cursor_bytes := rest; cursor_offset := 0 |}
          else
            {| cursor_bytes := byte :: rest;
               cursor_offset := S (cursor_offset cursor) |} in
        Some (bit, next_cursor)
      else None
  end.

Fixpoint read_bits_cursor (n : nat) (cursor : BitCursor) :
    option (list bool * BitCursor) :=
  match n with
  | 0 => Some ([], cursor)
  | S n' =>
      match read_bit_cursor cursor with
      | None => None
      | Some (bit, cursor') =>
          match read_bits_cursor n' cursor' with
          | None => None
          | Some (chunk, rest) => Some (bit :: chunk, rest)
          end
      end
  end.

Lemma read_bits_cursor_length :
  forall n cursor chunk rest,
    read_bits_cursor n cursor = Some (chunk, rest) ->
    length chunk = n.
Proof.
  induction n as [| n IH]; intros cursor chunk rest Hread; simpl in Hread.
  - inversion Hread; subst. reflexivity.
  - destruct (read_bit_cursor cursor) as [[bit cursor'] |] eqn:Hbit;
      [| discriminate].
    destruct (read_bits_cursor n cursor') as [[chunk_tail rest'] |]
      eqn:Htail; [| discriminate].
    inversion Hread; subst.
    simpl.
    apply f_equal.
    eapply IH.
    exact Htail.
Qed.

Fixpoint read_bits_nat_cursor_acc
    (n acc : nat)
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match n with
  | 0 => Some (acc, cursor)
  | S n' =>
      match read_bit_cursor cursor with
      | None => None
      | Some (bit, cursor') =>
          read_bits_nat_cursor_acc
            n'
            (2 * acc + if bit then 1 else 0)
            cursor'
      end
  end.

Definition read_bits_nat_cursor (n : nat) (cursor : BitCursor) :
    option (nat * BitCursor) :=
  read_bits_nat_cursor_acc n 0 cursor.

Definition read_u2_cursor (cursor : BitCursor) :
    option (nat * BitCursor) :=
  read_bits_nat_cursor 2 cursor.

Definition cursor_remaining_bits (cursor : BitCursor) : nat :=
  if cursor_offset cursor <? 8 then
    match cursor_bytes cursor with
    | [] => 0
    | _ :: rest => (8 - cursor_offset cursor) + 8 * length rest
    end
  else 0.

Fixpoint read_unary_depth_cursor_with_fuel
    (fuel : nat)
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match read_bit_cursor cursor with
      | None => None
      | Some (true, cursor') =>
          match read_unary_depth_cursor_with_fuel fuel' cursor' with
          | None => None
          | Some (depth, rest) => Some (S depth, rest)
          end
      | Some (false, rest) => Some (0, rest)
      end
  end.

Definition read_unary_depth_cursor (cursor : BitCursor) :
    option (nat * BitCursor) :=
  read_unary_depth_cursor_with_fuel
    (S (cursor_remaining_bits cursor)) cursor.

Definition read_natural_payload_cursor
    (width : nat)
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match read_bits_nat_cursor width cursor with
  | None => None
  | Some (suffix, rest) => Some (Nat.pow 2 width + suffix, rest)
  end.

Fixpoint decode_natural_loop_cursor
    (fuel depth width : nat)
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match read_natural_payload_cursor width cursor with
      | None => None
      | Some (n, rest) =>
          match depth with
          | 0 => Some (n, rest)
          | S depth' =>
              if 31 <? n then None
              else decode_natural_loop_cursor fuel' depth' n rest
          end
      end
  end.

Definition decode_natural_unbounded_cursor
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match read_unary_depth_cursor cursor with
  | None => None
  | Some (depth, rest) =>
      decode_natural_loop_cursor (S depth) depth 0 rest
  end.

Definition decode_natural_cursor
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match decode_natural_unbounded_cursor cursor with
  | None => None
  | Some (n, rest) =>
      if n <=? natural_max then Some (n, rest) else None
  end.

Definition decode_natural_bound_cursor
    (bound : option nat)
    (cursor : BitCursor) : option (nat * BitCursor) :=
  match decode_natural_cursor cursor with
  | None => None
  | Some (n, rest) =>
      match bound with
      | None => Some (n, rest)
      | Some max => if n <=? max then Some (n, rest) else None
      end
  end.

Definition decode_backref_cursor (index : nat) (cursor : BitCursor) :
    option (nat * BitCursor) :=
  match decode_natural_bound_cursor (Some index) cursor with
  | None => None
  | Some (offset, rest) => Some (index - offset, rest)
  end.

Definition read_hash256_cursor := read_bits_cursor 256.

Definition read_word_cursor (encoded_width : nat) (cursor : BitCursor) :
    option (list bool * BitCursor) :=
  match encoded_width with
  | 0 => None
  | S n => read_bits_cursor (Nat.pow 2 n) cursor
  end.

Fixpoint strip_prefix_cursor
    (prefix : list bool)
    (cursor : BitCursor) : option BitCursor :=
  match prefix with
  | [] => Some cursor
  | p :: prefix' =>
      match read_bit_cursor cursor with
      | None => None
      | Some (bit, cursor') =>
          if Bool.eqb p bit then strip_prefix_cursor prefix' cursor'
          else None
      end
  end.

Fixpoint try_decode_elements_jet_cursor
    (candidates : list ElementsJet)
    (cursor : BitCursor) : option (ElementsJet * BitCursor) :=
  match candidates with
  | [] => None
  | candidate :: rest =>
      match strip_prefix_cursor (bits_of_elements_jet candidate) cursor with
      | Some cursor' => Some (candidate, cursor')
      | None => try_decode_elements_jet_cursor rest cursor
      end
  end.

Definition decode_elements_jet_cursor (cursor : BitCursor) :
    option (ElementsJet * BitCursor) :=
  try_decode_elements_jet_cursor multisig_elements_jets cursor.

Definition decode_binary_node_cursor
    (index subcode : nat)
    (cursor : BitCursor) : option (RawNode * BitCursor) :=
  match decode_backref_cursor index cursor with
  | None => None
  | Some (lhs, cursor') =>
      match decode_backref_cursor index cursor' with
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

Definition decode_unary_node_cursor
    (index subcode : nat)
    (cursor : BitCursor) : option (RawNode * BitCursor) :=
  match decode_backref_cursor index cursor with
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

Definition decode_nullary_or_disconnect1_cursor
    (index subcode : nat)
    (cursor : BitCursor) : option (RawNode * BitCursor) :=
  match subcode with
  | 0 => Some (RIden, cursor)
  | 1 => Some (RUnit, cursor)
  | 2 => None
  | 3 => None
  | _ => None
  end.

Definition decode_raw_node_cursor (index : nat) (cursor : BitCursor) :
    option (RawNode * BitCursor) :=
  match read_bit_cursor cursor with
  | None => None
  | Some (true, cursor') =>
      match read_bit_cursor cursor' with
      | None => None
      | Some (true, cursor'') =>
          match decode_elements_jet_cursor cursor'' with
          | None => None
          | Some (jet, rest) => Some (RJet jet, rest)
          end
      | Some (false, cursor'') =>
          match decode_natural_bound_cursor (Some 32) cursor'' with
          | None => None
          | Some (encoded_width, cursor''') =>
              match read_word_cursor encoded_width cursor''' with
              | None => None
              | Some (value_bits, rest) =>
                  Some (RWord encoded_width value_bits, rest)
              end
          end
      end
  | Some (false, cursor') =>
      match read_u2_cursor cursor' with
      | None => None
      | Some (code, cursor'') =>
          match code with
          | 0 =>
              match read_u2_cursor cursor'' with
              | None => None
              | Some (subcode, rest) =>
                  decode_binary_node_cursor index subcode rest
              end
          | 1 =>
              match read_u2_cursor cursor'' with
              | None => None
              | Some (subcode, rest) =>
                  decode_unary_node_cursor index subcode rest
              end
          | 2 =>
              match read_u2_cursor cursor'' with
              | None => None
              | Some (subcode, rest) =>
                  decode_nullary_or_disconnect1_cursor index subcode rest
              end
          | 3 =>
              match read_bit_cursor cursor'' with
              | None => None
              | Some (true, rest) => Some (RWitness, rest)
              | Some (false, rest) =>
                  match read_hash256_cursor rest with
                  | None => None
                  | Some (cmr, rest') => Some (RHidden cmr, rest')
                  end
              end
          | _ => None
          end
      end
  end.

Fixpoint decode_raw_nodes_cursor
    (count index : nat)
    (cursor : BitCursor) : option (list RawNode * BitCursor) :=
  match count with
  | 0 => Some ([], cursor)
  | S count' =>
      match decode_raw_node_cursor index cursor with
      | None => None
      | Some (node, cursor') =>
          match decode_raw_nodes_cursor count' (S index) cursor' with
          | None => None
          | Some (nodes, rest) => Some (node :: nodes, rest)
          end
      end
  end.

Definition close_padding_cursor (cursor : BitCursor) : bool :=
  match cursor_bytes cursor with
  | [] => Nat.eqb (cursor_offset cursor) 0
  | byte :: rest =>
      (0 <? cursor_offset cursor) &&
      (cursor_offset cursor <? 8) &&
      match rest with
      | [] => all_false (skipn (cursor_offset cursor) (bits_of_byte byte))
      | _ :: _ => false
      end
  end.

Definition decode_program_bytes_streaming (bytes : list byte) :
    option (list RawNode) :=
  match decode_natural_bound_cursor (Some dag_len_max) (cursor_start bytes) with
  | None => None
  | Some (count, cursor') =>
      match decode_raw_nodes_cursor count 0 cursor' with
      | None => None
      | Some (nodes, rest) =>
          if close_padding_cursor rest then Some nodes else None
      end
  end.

Definition decode_structural_program_bytes_streaming (bytes : list byte) :
    option StructuralProgram :=
  match decode_program_bytes_streaming bytes with
  | Some raw => validate_raw_program raw
  | None => None
  end.
