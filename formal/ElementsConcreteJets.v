(*
  ElementsConcreteJets.v — G4 step 2: an executable concrete interpretation of
  the whitelisted Elements jets, suitable for running the deployed multisig
  program inside Coq with SimplicityStructuralEval.v.

  Word values follow the jet arrows in ElementsJetTypes.v exactly (words are
  MSB-first balanced bit trees; optional words are unit + word with None on the
  left).  SHA-256 streaming contexts use the Simplicity Ctx8 shape
  ((mw256 x (mw128 x (mw64 x (mw32 x (mw16 x mw8))))) x (w64 x w256)): the
  buffer holds the pending (uncompressed) message prefix split into
  present/absent chunks by the binary decomposition of its length, largest
  chunk first; the w64 counts total message bytes added; the w256 is the real
  SHA-256 midstate (Sha256Core.v).  Compression, padding and finalization are
  the genuine FIPS 180-4 operations.

  Abstractions (documented, mirroring the abstract model's trust boundary):
  - bip_0340_verify is interpreted against an explicit finite table of valid
    (pubkey, message, signature) bit triples — exactly the shape of the
    abstract [signature_valid] predicate in the model.  No elliptic-curve
    arithmetic is claimed.
  - build_taptweak is interpreted as the BIP-341-style tagged-hash commitment
    of (internal key, merkle root); the final key-tweaking point addition is
    abstracted away.  build_tapbranch sorts its children lexicographically and
    applies the TapBranch tagged hash; tapdata_init yields the TapData tagged
    midstate.  These are internally consistent: the concrete environments in
    CompiledMultisigExecution.v commit to vote scripts through these same
    functions.

  PROOF-STYLE CONSTRAINT (memory): no [Set Implicit Arguments]/[Set Strict
  Implicit] in files touching the concrete artifact.
*)

From Coq Require Import NArith List Bool Arith.
From MultisigFormal Require Import
  ElementsJets SimplicityByteDecoder SimplicityStructuralEval Sha256Core
  SimplicityCmrSha.

Import ListNotations.

(* ---------- bit/byte helpers (N-native) ---------- *)

Fixpoint bits_of_N_be (width : nat) (x : N) : list bool :=
  match width with
  | 0 => []
  | S width' => N.testbit x (N.of_nat width') :: bits_of_N_be width' x
  end.

Definition N_of_bits (bits : list bool) : N :=
  fold_left (fun (acc : N) (b : bool) => (2 * acc + (if b then 1 else 0))%N)
    bits 0%N.

Definition byte_bits (b : N) : list bool := bits_of_N_be 8 b.

Definition bytes_to_bitsN (bs : list N) : list bool :=
  concat (map byte_bits bs).

Fixpoint bytes_of_bitsN (bits : list bool) : list N :=
  match bits with
  | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: rest =>
      N_of_bits [b7; b6; b5; b4; b3; b2; b1; b0] :: bytes_of_bitsN rest
  | _ => []
  end.

Definition value_of_bytes (log_width : nat) (bs : list N) : SValue :=
  value_of_bits log_width (bytes_to_bitsN bs).

Definition bytes_of_value (log_width : nat) (v : SValue) : option (list N) :=
  match bits_of_value log_width v with
  | Some bits => Some (bytes_of_bitsN bits)
  | None => None
  end.

Definition value_of_N (log_width width : nat) (x : N) : SValue :=
  value_of_bits log_width (bits_of_N_be width x).

Definition N_of_value (log_width : nat) (v : SValue) : option N :=
  match bits_of_value log_width v with
  | Some bits => Some (N_of_bits bits)
  | None => None
  end.

Fixpoint bytes_le (a b : list N) : bool :=
  match a, b with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if (x <? y)%N then true
      else if (y <? x)%N then false
      else bytes_le xs ys
  end.

(* ---------- streaming SHA-256 contexts ---------- *)

Record ShadowCtx := {
  ctx_buffer : list N;   (* pending bytes, length < 64 *)
  ctx_count : N;         (* total message bytes added *)
  ctx_state : state      (* real SHA-256 midstate *)
}.

Fixpoint compress_blocks (fuel : nat) (st : state) (bs : list N) :
    state * list N :=
  match fuel with
  | 0 => (st, bs)
  | S fuel' =>
      if 64 <=? length bs
      then compress_blocks fuel' (compress st (firstn 64 bs)) (skipn 64 bs)
      else (st, bs)
  end.

Definition shadow_init : ShadowCtx :=
  {| ctx_buffer := []; ctx_count := 0%N; ctx_state := H0const |}.

Definition shadow_add (c : ShadowCtx) (bs : list N) : ShadowCtx :=
  let combined := ctx_buffer c ++ bs in
  let result := compress_blocks (S (length combined / 64)) (ctx_state c) combined in
  {| ctx_buffer := snd result;
     ctx_count := (ctx_count c + N.of_nat (length bs))%N;
     ctx_state := fst result |}.

Definition shadow_finalize (c : ShadowCtx) : list N :=
  let bitlen := (8 * ctx_count c)%N in
  let tail := ctx_buffer c ++ [128%N] in
  let zeros :=
    if length tail <=? 56 then 56 - length tail else 120 - length tail in
  let full := tail ++ repeat 0%N zeros ++ n_to_bytes_be 8 bitlen in
  let result := compress_blocks (S (length full / 64)) (ctx_state c) full in
  state_to_bytes (fst result).

(* BIP-340-style tagged-hash context: midstate after one block of
   H(tag) || H(tag); 64 bytes already counted. *)
Definition tagged_ctx (tag_bytes : list N) : ShadowCtx :=
  {| ctx_buffer := [];
     ctx_count := 64%N;
     ctx_state := bytes32_to_state (bip340_iv_of tag_bytes) |}.

Definition tagged_hash (tag_bytes msg : list N) : list N :=
  shadow_finalize (shadow_add (tagged_ctx tag_bytes) msg).

(* "TapData/elements", "TapBranch/elements", "TapTweak/elements" *)
Definition tapdata_tag : list N :=
  [84; 97; 112; 68; 97; 116; 97;
   47; 101; 108; 101; 109; 101; 110; 116; 115]%N.
Definition tapbranch_tag : list N :=
  [84; 97; 112; 66; 114; 97; 110; 99; 104;
   47; 101; 108; 101; 109; 101; 110; 116; 115]%N.
Definition taptweak_tag : list N :=
  [84; 97; 112; 84; 119; 101; 97; 107;
   47; 101; 108; 101; 109; 101; 110; 116; 115]%N.

Definition build_tapbranch_bytes (l r : list N) : list N :=
  if bytes_le l r
  then tagged_hash tapbranch_tag (l ++ r)
  else tagged_hash tapbranch_tag (r ++ l).

Definition build_taptweak_bytes (key node : list N) : list N :=
  tagged_hash taptweak_tag (key ++ node).

(* ---------- Ctx8 <-> SValue codec ---------- *)

(* Chunk sizes largest-first: 32, 16, 8, 4, 2, 1 bytes
   (word log-widths 8, 7, 6, 5, 4, 3). *)
Definition encode_chunk (byte_count log_width : nat) (present : bool)
    (bs : list N) : SValue * list N :=
  if present
  then (VRight (value_of_bytes log_width (firstn byte_count bs)),
        skipn byte_count bs)
  else (VLeft VUnit, bs).

Definition encode_ctx8 (c : ShadowCtx) : SValue :=
  let len := length (ctx_buffer c) in
  (* presence of each chunk = corresponding bit of the buffer length *)
  let b5 := Nat.testbit len 5 in
  let b4 := Nat.testbit len 4 in
  let b3 := Nat.testbit len 3 in
  let b2 := Nat.testbit len 2 in
  let b1 := Nat.testbit len 1 in
  let b0 := Nat.testbit len 0 in
  let r0 := encode_chunk 32 8 b5 (ctx_buffer c) in
  let r1 := encode_chunk 16 7 b4 (snd r0) in
  let r2 := encode_chunk 8 6 b3 (snd r1) in
  let r3 := encode_chunk 4 5 b2 (snd r2) in
  let r4 := encode_chunk 2 4 b1 (snd r3) in
  let r5 := encode_chunk 1 3 b0 (snd r4) in
  VPair
    (VPair (fst r0)
      (VPair (fst r1)
        (VPair (fst r2)
          (VPair (fst r3)
            (VPair (fst r4) (fst r5))))))
    (VPair (value_of_N 6 64 (ctx_count c))
           (value_of_bytes 8 (state_to_bytes (ctx_state c)))).

Definition decode_chunk (log_width : nat) (v : SValue) : option (list N) :=
  match v with
  | VLeft VUnit => Some []
  | VRight w => bytes_of_value log_width w
  | _ => None
  end.

Definition decode_ctx8 (v : SValue) : option ShadowCtx :=
  match v with
  | VPair
      (VPair m32 (VPair m16 (VPair m8 (VPair m4 (VPair m2 m1)))))
      (VPair count mid) =>
      match decode_chunk 8 m32, decode_chunk 7 m16, decode_chunk 6 m8,
            decode_chunk 5 m4, decode_chunk 4 m2, decode_chunk 3 m1,
            N_of_value 6 count, bytes_of_value 8 mid with
      | Some c32, Some c16, Some c8, Some c4, Some c2, Some c1,
        Some n, Some mid_bytes =>
          Some {| ctx_buffer := c32 ++ c16 ++ c8 ++ c4 ++ c2 ++ c1;
                  ctx_count := n;
                  ctx_state := bytes32_to_state mid_bytes |}
      | _, _, _, _, _, _, _, _ => None
      end
  | _ => None
  end.

(* ---------- concrete environment ---------- *)

Record ConcreteEnv := {
  cenv_num_inputs : N;
  cenv_current_index : N;
  cenv_current_script_hash : list N;        (* 32 bytes *)
  cenv_input_script_hashes : list (list N); (* 32 bytes each, by index *)
  cenv_input_hashes : list (list N);
  cenv_output_hashes : list (list N)
}.

Definition optional_hash_value (entries : list (list N)) (index : N) : SValue :=
  match nth_error entries (N.to_nat index) with
  | Some bytes => VRight (value_of_bytes 8 bytes)
  | None => VLeft VUnit
  end.

(* ---------- signature table (the concrete signature_valid) ---------- *)

Definition SigTriple : Type := list bool * list bool * list bool.

Definition sig_triple_matches (pk msg sig : list bool) (t : SigTriple) : bool :=
  match t with
  | (tpk, tmsg, tsig) =>
      bits_eqb pk tpk && bits_eqb msg tmsg && bits_eqb sig tsig
  end.

Definition sig_table_contains
    (table : list SigTriple) (pk msg sig : list bool) : bool :=
  existsb (sig_triple_matches pk msg sig) table.

(* ---------- the concrete jet interpretation ---------- *)

Definition eval_bit (b : bool) : EvalResult := EValue (value_of_bit b).

Definition concrete_jet_sem
    (table : list SigTriple)
    (env : ConcreteEnv)
    (jet : ElementsJet)
    (input : SValue) : EvalResult :=
  match jet with
  | JAdd32 =>
      match input with
      | VPair x y =>
          match N_of_value 5 x, N_of_value 5 y with
          | Some nx, Some ny =>
              let sum := (nx + ny)%N in
              EValue (VPair (value_of_bit (2 ^ 32 <=? sum)%N)
                            (value_of_N 5 32 (sum mod 2 ^ 32)))
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JIncrement32 =>
      match N_of_value 5 input with
      | Some nx =>
          let sum := (nx + 1)%N in
          EValue (VPair (value_of_bit (2 ^ 32 <=? sum)%N)
                        (value_of_N 5 32 (sum mod 2 ^ 32)))
      | None => EStuck
      end
  | JLe32 =>
      match input with
      | VPair x y =>
          match N_of_value 5 x, N_of_value 5 y with
          | Some nx, Some ny => eval_bit (nx <=? ny)%N
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JLt32 =>
      match input with
      | VPair x y =>
          match N_of_value 5 x, N_of_value 5 y with
          | Some nx, Some ny => eval_bit (nx <? ny)%N
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JEq1 =>
      match input with
      | VPair x y =>
          match bits_of_value 0 x, bits_of_value 0 y with
          | Some bx, Some by' => eval_bit (bits_eqb bx by')
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JEq16 =>
      match input with
      | VPair x y =>
          match bits_of_value 4 x, bits_of_value 4 y with
          | Some bx, Some by' => eval_bit (bits_eqb bx by')
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JEq32 =>
      match input with
      | VPair x y =>
          match bits_of_value 5 x, bits_of_value 5 y with
          | Some bx, Some by' => eval_bit (bits_eqb bx by')
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JEq256 =>
      match input with
      | VPair x y =>
          match bits_of_value 8 x, bits_of_value 8 y with
          | Some bx, Some by' => eval_bit (bits_eqb bx by')
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JLeftPadLow8_32 =>
      match bits_of_value 3 input with
      | Some bits => EValue (value_of_bits 5 (repeat false 24 ++ bits))
      | None => EStuck
      end
  | JLeftPadLow16_32 =>
      match bits_of_value 4 input with
      | Some bits => EValue (value_of_bits 5 (repeat false 16 ++ bits))
      | None => EStuck
      end
  | JVerify =>
      match input with
      | VRight VUnit => EValue VUnit
      | VLeft VUnit => EFail
      | _ => EStuck
      end
  | JCurrentIndex =>
      match input with
      | VUnit => EValue (value_of_N 5 32 (cenv_current_index env))
      | _ => EStuck
      end
  | JNumInputs =>
      match input with
      | VUnit => EValue (value_of_N 5 32 (cenv_num_inputs env))
      | _ => EStuck
      end
  | JCurrentScriptHash =>
      match input with
      | VUnit => EValue (value_of_bytes 8 (cenv_current_script_hash env))
      | _ => EStuck
      end
  | JInputScriptHash =>
      match N_of_value 5 input with
      | Some index =>
          EValue (optional_hash_value (cenv_input_script_hashes env) index)
      | None => EStuck
      end
  | JInputHash =>
      match N_of_value 5 input with
      | Some index =>
          EValue (optional_hash_value (cenv_input_hashes env) index)
      | None => EStuck
      end
  | JOutputHash =>
      match N_of_value 5 input with
      | Some index =>
          EValue (optional_hash_value (cenv_output_hashes env) index)
      | None => EStuck
      end
  | JSha256Ctx8Init =>
      match input with
      | VUnit => EValue (encode_ctx8 shadow_init)
      | _ => EStuck
      end
  | JTapdataInit =>
      match input with
      | VUnit => EValue (encode_ctx8 (tagged_ctx tapdata_tag))
      | _ => EStuck
      end
  | JSha256Ctx8Add2 =>
      match input with
      | VPair ctx msg =>
          match decode_ctx8 ctx, bytes_of_value 4 msg with
          | Some c, Some bs => EValue (encode_ctx8 (shadow_add c bs))
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JSha256Ctx8Add32 =>
      match input with
      | VPair ctx msg =>
          match decode_ctx8 ctx, bytes_of_value 8 msg with
          | Some c, Some bs => EValue (encode_ctx8 (shadow_add c bs))
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JSha256Ctx8Add64 =>
      match input with
      | VPair ctx msg =>
          match decode_ctx8 ctx, bytes_of_value 9 msg with
          | Some c, Some bs => EValue (encode_ctx8 (shadow_add c bs))
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JSha256Ctx8Finalize =>
      match decode_ctx8 input with
      | Some c => EValue (value_of_bytes 8 (shadow_finalize c))
      | None => EStuck
      end
  | JBuildTapbranch =>
      match input with
      | VPair l r =>
          match bytes_of_value 8 l, bytes_of_value 8 r with
          | Some lb, Some rb =>
              EValue (value_of_bytes 8 (build_tapbranch_bytes lb rb))
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JBuildTaptweak =>
      match input with
      | VPair key node =>
          match bytes_of_value 8 key, bytes_of_value 8 node with
          | Some kb, Some nb =>
              EValue (value_of_bytes 8 (build_taptweak_bytes kb nb))
          | _, _ => EStuck
          end
      | _ => EStuck
      end
  | JBip0340Verify =>
      match input with
      | VPair (VPair pk msg) sig =>
          match bits_of_value 8 pk, bits_of_value 8 msg,
                bits_of_value 9 sig with
          | Some pkb, Some msgb, Some sigb =>
              if sig_table_contains table pkb msgb sigb
              then EValue VUnit
              else EFail
          | _, _, _ => EStuck
          end
      | _ => EStuck
      end
  end.
