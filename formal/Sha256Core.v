(*
  Sha256Core.v — a self-contained, pure-Rocq SHA-256.

  This is Step 1 of the G5 "byte-level artifact proof" route (Route B): a SHA-256
  implementation that depends on nothing but the Rocq standard library, so it can
  be instantiated as the concrete commitment-Merkle-root hash for the Simplicity
  byte decoder WITHOUT importing the upstream VST/CompCert SHA development (which
  is pinned to Coq 8.17 and cannot be loaded into this Rocq 9.1 audit).

  32-bit words are represented with [N] (binary naturals); Coq's [nat] is unary,
  so a 2^32 mask as [nat] would be intractable. All word arithmetic is reduced
  mod 2^32 by [w32].

  Correctness is anchored to the published FIPS 180-4 test vectors, proved by
  [vm_compute] at the bottom of the file. Later steps (SimplicityCmrSha.v) build
  the Simplicity tag/compress layer on top and byte-pin the combinator tags to
  the upstream constants, exactly as ElementsJetCmr.v does for the jet CMRs.
*)

From Coq Require Import NArith List.
Import ListNotations.

(* A 32-bit word, kept reduced mod 2^32 by [w32]. *)
Definition word := N.

Definition mask32 : word := 4294967295%N.          (* 2^32 - 1 *)
Definition w32 (x : N) : word := N.land x mask32.
Definition add32 (x y : word) : word := w32 (N.add x y).

(* Right-rotate and right-shift of a 32-bit word by [n] bit positions. *)
Definition rotr (n : nat) (x : word) : word :=
  w32 (N.lor (N.shiftr x (N.of_nat n))
             (N.shiftl x (N.of_nat (32 - n)))).
Definition shr (n : nat) (x : word) : word := N.shiftr x (N.of_nat n).

Definition bsig0 (x : word) : word := N.lxor (rotr 2 x)  (N.lxor (rotr 13 x) (rotr 22 x)).
Definition bsig1 (x : word) : word := N.lxor (rotr 6 x)  (N.lxor (rotr 11 x) (rotr 25 x)).
Definition ssig0 (x : word) : word := N.lxor (rotr 7 x)  (N.lxor (rotr 18 x) (shr 3 x)).
Definition ssig1 (x : word) : word := N.lxor (rotr 17 x) (N.lxor (rotr 19 x) (shr 10 x)).

Definition ch  (x y z : word) : word :=
  N.lxor (N.land x y) (N.land (N.lxor x mask32) z).
Definition maj (x y z : word) : word :=
  N.lxor (N.land x y) (N.lxor (N.land x z) (N.land y z)).

(* The 64 SHA-256 round constants (FIPS 180-4, section 4.2.2). *)
Definition K_list : list word :=
  [ 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5
  ; 0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174
  ; 0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da
  ; 0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967
  ; 0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85
  ; 0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070
  ; 0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3
  ; 0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ]%N.

(* The eight-word chaining state, left-nested to match Coq tuple patterns. *)
Definition state := (word * word * word * word * word * word * word * word)%type.

(* Initial hash value (FIPS 180-4, section 5.3.3). *)
Definition H0const : state :=
  ( 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
  , 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 )%N.

(* Big-endian assembly of four bytes into one 32-bit word. *)
Definition be4 (b0 b1 b2 b3 : N) : word :=
  w32 ((b0 * 16777216 + b1 * 65536 + b2 * 256 + b3)%N).

(* 64 message bytes -> 16 big-endian words. Non-multiples of 4 truncate; blocks
   are always exactly 64 bytes so this yields 16 words. *)
Fixpoint bytes_to_words (bs : list N) : list word :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => be4 b0 b1 b2 b3 :: bytes_to_words rest
  | _ => []
  end.

(* Extend the 16 block words to the full 64-word message schedule.  [fuel] is the
   number of words still to append (48 for a full schedule); [w] starts as the 16
   block words and grows to length 64. *)
Fixpoint build_schedule (fuel : nat) (w : list word) : list word :=
  match fuel with
  | O => w
  | S f =>
      let t := length w in
      let wt := add32 (add32 (ssig1 (nth (t - 2) w 0%N)) (nth (t - 7) w 0%N))
                      (add32 (ssig0 (nth (t - 15) w 0%N)) (nth (t - 16) w 0%N)) in
      build_schedule f (w ++ [wt])
  end.

(* The 64 compression rounds, driven by the index list [ts] = seq 0 64. *)
Fixpoint rounds (ts : list nat) (st : state) (w : list word) : state :=
  match ts with
  | [] => st
  | t :: rest =>
      let '(a, b, c, d, e, f, g, h) := st in
      let t1 := add32 (add32 (add32 h (bsig1 e)) (add32 (ch e f g) (nth t K_list 0%N)))
                      (nth t w 0%N) in
      let t2 := add32 (bsig0 a) (maj a b c) in
      rounds rest (add32 t1 t2, a, b, c, add32 d t1, e, f, g) w
  end.

(* Run the message schedule and 64 rounds over 16 block words, then feed-forward.
   This is the raw SHA-256 block compression.  The Simplicity CMR layer
   (SimplicityCmrSha.v) calls it directly from a midstate IV. *)
Definition compress_words (st : state) (w16 : list word) : state :=
  let w := build_schedule 48 w16 in
  let '(a, b, c, d, e, f, g, h) := rounds (seq 0 64) st w in
  let '(a0, b0, c0, d0, e0, f0, g0, h0) := st in
  ( add32 a0 a, add32 b0 b, add32 c0 c, add32 d0 d
  , add32 e0 e, add32 f0 f, add32 g0 g, add32 h0 h ).

(* Process one 64-byte block. *)
Definition compress (st : state) (block : list N) : state :=
  compress_words st (bytes_to_words block).

(* Big-endian byte serialization of an [N] into exactly [nbytes] bytes. *)
Definition n_to_bytes_be (nbytes : nat) (x : N) : list N :=
  map (fun i => N.land (N.shiftr x (N.of_nat (8 * (nbytes - 1 - i)))) 255%N)
      (seq 0 nbytes).

(* The final 8-word state as 32 big-endian bytes. *)
Definition state_to_bytes (st : state) : list N :=
  let '(a, b, c, d, e, f, g, h) := st in
  flat_map (n_to_bytes_be 4) [a; b; c; d; e; f; g; h].

(* SHA-256 padding: 0x80, then zero bytes, then the 64-bit big-endian bit length. *)
Definition sha256_pad (msg : list N) : list N :=
  let len := length msg in
  let bitlen := (N.of_nat len * 8)%N in
  let zeros := Nat.modulo (64 - Nat.modulo (len + 9) 64) 64 in
  msg ++ [128%N] ++ repeat 0%N zeros ++ n_to_bytes_be 8 bitlen.

(* Fold [compress] over the [fuel]-many 64-byte blocks of [bs]. *)
Fixpoint process (fuel : nat) (st : state) (bs : list N) : state :=
  match fuel with
  | O => st
  | S f => process f (compress st (firstn 64 bs)) (skipn 64 bs)
  end.

(* SHA-256 of a byte list; input and output bytes are [N] in [0,256). *)
Definition sha256 (msg : list N) : list N :=
  let padded := sha256_pad msg in
  state_to_bytes (process (Nat.div (length padded) 64) H0const padded).

(* The digest is always 32 bytes, independent of the message — useful for the
   256-bit CmrBits obligations in later steps. *)
Lemma state_to_bytes_length : forall st, length (state_to_bytes st) = 32%nat.
Proof. intros st; destruct st as [[[[[[[a b] c] d] e] f] g] h]; reflexivity. Qed.

Lemma sha256_length : forall msg, length (sha256 msg) = 32%nat.
Proof. intros msg; unfold sha256; apply state_to_bytes_length. Qed.

(* ---- FIPS 180-4 known-answer tests (the trust anchor for this file). ---- *)

(* SHA256("") = e3b0c442 98fc1c14 9afbf4c8 996fb924 27ae41e4 649b934c a495991b 7852b855 *)
Example sha256_empty :
  sha256 [] =
  [ 0xe3;0xb0;0xc4;0x42;0x98;0xfc;0x1c;0x14;0x9a;0xfb;0xf4;0xc8;0x99;0x6f;0xb9;0x24
  ; 0x27;0xae;0x41;0xe4;0x64;0x9b;0x93;0x4c;0xa4;0x95;0x99;0x1b;0x78;0x52;0xb8;0x55 ]%N.
Proof. vm_compute. reflexivity. Qed.

(* SHA256("abc") = ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad *)
Example sha256_abc :
  sha256 [ 0x61; 0x62; 0x63 ]%N =
  [ 0xba;0x78;0x16;0xbf;0x8f;0x01;0xcf;0xea;0x41;0x41;0x40;0xde;0x5d;0xae;0x22;0x23
  ; 0xb0;0x03;0x61;0xa3;0x96;0x17;0x7a;0x9c;0xb4;0x10;0xff;0x61;0xf2;0x00;0x15;0xad ]%N.
Proof. vm_compute. reflexivity. Qed.

(* SHA256 of the 56-byte two-block NIST vector
   "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
   = 248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1 *)
Example sha256_two_block :
  sha256 [ 0x61;0x62;0x63;0x64; 0x62;0x63;0x64;0x65; 0x63;0x64;0x65;0x66; 0x64;0x65;0x66;0x67
         ; 0x65;0x66;0x67;0x68; 0x66;0x67;0x68;0x69; 0x67;0x68;0x69;0x6a; 0x68;0x69;0x6a;0x6b
         ; 0x69;0x6a;0x6b;0x6c; 0x6a;0x6b;0x6c;0x6d; 0x6b;0x6c;0x6d;0x6e; 0x6c;0x6d;0x6e;0x6f
         ; 0x6d;0x6e;0x6f;0x70; 0x6e;0x6f;0x70;0x71 ]%N =
  [ 0x24;0x8d;0x6a;0x61;0xd2;0x06;0x38;0xb8;0xe5;0xc0;0x26;0x93;0x0c;0x3e;0x60;0x39
  ; 0xa3;0x3c;0xe4;0x59;0x64;0xff;0x21;0x67;0xf6;0xec;0xed;0xd4;0x19;0xdb;0x06;0xc1 ]%N.
Proof. vm_compute. reflexivity. Qed.
