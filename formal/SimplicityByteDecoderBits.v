From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import ElementsJets.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Executable Coq skeleton for the Simplicity program byte decoder.

  This mirrors the structural part of rust-simplicity's bit_encoding/decode.rs:
  bytes are read MSB-first, a positive natural gives the node count, then each
  node is decoded in canonical order using positive backreferences to earlier
  nodes. Jet decoding is intentionally restricted to ElementsJets.v's multisig
  jet subset.

  This file does not yet type-check or semantically interpret the decoded DAG.
  It is the first byte-level artifact needed to replace exporter trust.
*)

Definition byte := nat.
Definition dag_len_max : nat := 8000 * 1000.
Definition natural_max : nat := Nat.pow 2 31 - 1.

Definition bits_of_byte (b : byte) : list bool :=
  bits_of_nat 8 b.

Definition bytes_to_bits (bytes : list byte) : list bool :=
  concat (map bits_of_byte bytes).

Definition read_bit (bits : list bool) : option (bool * list bool) :=
  match bits with
  | [] => None
  | bit :: rest => Some (bit, rest)
  end.

Fixpoint read_bits (n : nat) (bits : list bool) :
    option (list bool * list bool) :=
  match n with
  | 0 => Some ([], bits)
  | S n' =>
      match read_bit bits with
      | None => None
      | Some (bit, bits') =>
          match read_bits n' bits' with
          | None => None
          | Some (chunk, rest) => Some (bit :: chunk, rest)
          end
      end
  end.

Lemma read_bits_length :
  forall n bits chunk rest,
    read_bits n bits = Some (chunk, rest) ->
    length chunk = n.
Proof.
  induction n as [| n IH]; intros bits chunk rest Hread; simpl in Hread.
  - inversion Hread; subst. reflexivity.
  - destruct (read_bit bits) as [[bit bits'] |] eqn:Hbit;
      [| discriminate].
    destruct (read_bits n bits') as [[chunk_tail rest'] |] eqn:Htail;
      [| discriminate].
    inversion Hread; subst.
    simpl.
    apply f_equal.
    eapply IH.
    exact Htail.
Qed.

Fixpoint read_bits_nat_acc (n acc : nat) (bits : list bool) :
    option (nat * list bool) :=
  match n with
  | 0 => Some (acc, bits)
  | S n' =>
      match read_bit bits with
      | None => None
      | Some (bit, bits') =>
          read_bits_nat_acc
            n'
            (2 * acc + if bit then 1 else 0)
            bits'
      end
  end.

Definition read_bits_nat (n : nat) (bits : list bool) :
    option (nat * list bool) :=
  read_bits_nat_acc n 0 bits.

Definition read_u2 (bits : list bool) : option (nat * list bool) :=
  read_bits_nat 2 bits.

Fixpoint read_unary_depth_with_fuel
    (fuel : nat)
    (bits : list bool) : option (nat * list bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match read_bit bits with
      | None => None
      | Some (true, bits') =>
          match read_unary_depth_with_fuel fuel' bits' with
          | None => None
          | Some (depth, rest) => Some (S depth, rest)
          end
      | Some (false, rest) => Some (0, rest)
      end
  end.

Definition read_unary_depth (bits : list bool) : option (nat * list bool) :=
  read_unary_depth_with_fuel (S (length bits)) bits.

Definition read_natural_payload (width : nat) (bits : list bool) :
    option (nat * list bool) :=
  match read_bits_nat width bits with
  | None => None
  | Some (suffix, rest) => Some (Nat.pow 2 width + suffix, rest)
  end.

Lemma pow2_positive :
  forall width,
    1 <= Nat.pow 2 width.
Proof.
  induction width as [| width IH]; simpl; lia.
Qed.

Lemma read_natural_payload_positive :
  forall width bits n rest,
    read_natural_payload width bits = Some (n, rest) ->
    1 <= n.
Proof.
  intros width bits n rest Hread.
  unfold read_natural_payload in Hread.
  destruct (read_bits_nat width bits) as [[suffix rest'] |] eqn:Hbits;
    [| discriminate].
  inversion Hread; subst.
  pose proof (pow2_positive width) as Hpow.
  lia.
Qed.

Fixpoint decode_natural_loop
    (fuel depth width : nat)
    (bits : list bool) : option (nat * list bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match read_natural_payload width bits with
      | None => None
      | Some (n, rest) =>
          match depth with
          | 0 => Some (n, rest)
          | S depth' =>
              if 31 <? n then None
              else decode_natural_loop fuel' depth' n rest
          end
      end
  end.

Definition decode_natural_unbounded
    (bits : list bool) : option (nat * list bool) :=
  match read_unary_depth bits with
  | None => None
  | Some (depth, rest) =>
      decode_natural_loop (S depth) depth 0 rest
  end.

Definition decode_natural (bits : list bool) : option (nat * list bool) :=
  match decode_natural_unbounded bits with
  | None => None
  | Some (n, rest) =>
      if n <=? natural_max then Some (n, rest) else None
  end.

Theorem decode_natural_some_bound :
  forall bits n rest,
    decode_natural bits = Some (n, rest) ->
    n <= natural_max.
Proof.
  intros bits n rest Hdecode.
  unfold decode_natural in Hdecode.
  destruct (decode_natural_unbounded bits) as [[decoded rest'] |]
    eqn:Hnatural; [| discriminate].
  destruct (decoded <=? natural_max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  apply Nat.leb_le in Hbound.
  exact Hbound.
Qed.

Lemma decode_natural_loop_positive :
  forall fuel depth width bits n rest,
    decode_natural_loop fuel depth width bits = Some (n, rest) ->
    1 <= n.
Proof.
  induction fuel as [| fuel IH];
    intros depth width bits n rest Hdecode; simpl in Hdecode.
  - discriminate.
  - destruct (read_natural_payload width bits)
      as [[payload bits_after_payload] |] eqn:Hpayload;
      [| discriminate].
    destruct depth as [| depth'].
    + inversion Hdecode; subst.
      eapply read_natural_payload_positive.
      exact Hpayload.
    + destruct (31 <? payload) eqn:Hpayload_bound; [discriminate |].
      eapply IH.
      exact Hdecode.
Qed.

Theorem decode_natural_some_positive :
  forall bits n rest,
    decode_natural bits = Some (n, rest) ->
    1 <= n.
Proof.
  intros bits n rest Hdecode.
  unfold decode_natural in Hdecode.
  destruct (decode_natural_unbounded bits)
    as [[decoded rest'] |] eqn:Hunbounded; [| discriminate].
  destruct (decoded <=? natural_max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  unfold decode_natural_unbounded in Hunbounded.
  destruct (read_unary_depth bits) as [[depth bits_after_depth] |]
    eqn:Hdepth; [| discriminate].
  eapply decode_natural_loop_positive.
  exact Hunbounded.
Qed.

Definition decode_natural_bound
    (bound : option nat)
    (bits : list bool) : option (nat * list bool) :=
  match decode_natural bits with
  | None => None
  | Some (n, rest) =>
      match bound with
      | None => Some (n, rest)
      | Some max => if n <=? max then Some (n, rest) else None
      end
  end.

Lemma decode_natural_bound_some :
  forall max bits n rest,
    decode_natural_bound (Some max) bits = Some (n, rest) ->
    n <= max.
Proof.
  intros max bits n rest Hdecode.
  unfold decode_natural_bound in Hdecode.
  destruct (decode_natural bits) as [[decoded rest'] |] eqn:Hnatural;
    [| discriminate].
  destruct (decoded <=? max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  apply Nat.leb_le in Hbound.
  exact Hbound.
Qed.

Lemma decode_natural_bound_some_positive :
  forall max bits n rest,
    decode_natural_bound (Some max) bits = Some (n, rest) ->
    1 <= n.
Proof.
  intros max bits n rest Hdecode.
  unfold decode_natural_bound in Hdecode.
  destruct (decode_natural bits) as [[decoded rest'] |] eqn:Hnatural;
    [| discriminate].
  destruct (decoded <=? max) eqn:Hbound; [| discriminate].
  inversion Hdecode; subst.
  eapply decode_natural_some_positive.
  exact Hnatural.
Qed.

Definition decode_backref (index : nat) (bits : list bool) :
    option (nat * list bool) :=
  match decode_natural_bound (Some index) bits with
  | None => None
  | Some (offset, rest) => Some (index - offset, rest)
  end.

Lemma decode_backref_child_lt :
  forall index bits child rest,
    decode_backref index bits = Some (child, rest) ->
    child < index.
Proof.
  intros index bits child rest Hdecode.
  unfold decode_backref in Hdecode.
  destruct (decode_natural_bound (Some index) bits)
    as [[offset rest'] |] eqn:Hoffset; [| discriminate].
  pose proof
    (@decode_natural_bound_some index bits offset rest' Hoffset)
    as Hoffset_le.
  pose proof
    (@decode_natural_bound_some_positive index bits offset rest' Hoffset)
    as Hoffset_positive.
  inversion Hdecode; subst.
  lia.
Qed.

Definition read_hash256 := read_bits 256.
Definition read_word (encoded_width : nat) (bits : list bool) :
    option (list bool * list bool) :=
  match encoded_width with
  | 0 => None
  | S n => read_bits (Nat.pow 2 n) bits
  end.
