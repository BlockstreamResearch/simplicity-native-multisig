(*
  SimplicityCmrAlgebra.v — Step 4b of G5 Route B.

  Instantiate the byte decoder's abstract `CmrAlgebra` (over CmrBits = list bool)
  with the concrete SHA-256 Simplicity CMR of SimplicityCmrSha.v.  This is the
  first concrete, SHA-256-backed CmrAlgebra in the tree; every prior use was the
  degenerate `zero_cmr_alg` or `toy_cmr_alg`.  Feeding `simplicity_cmr_algebra`
  to the decoder's CMR checker lets Coq compute the REAL commitment Merkle root
  of the decoded program and compare it to the exported 32-byte CMR, with no
  exporter or foundation trust.

  Bridge: the decoder represents every hash as CmrBits (list bool, MSB-first per
  byte, per bits_of_nat).  Our SHA layer works on list N bytes.  cmrbits_of_bytes
  and bytes_of_bits convert between them and are mutual inverses on 32-byte data.
*)

From Coq Require Import NArith List.
From MultisigFormal Require Import
  SimplicityByteDecoderCmrCore SimplicityByteDecoderBits
  ElementsJets ElementsJetCmr SimplicityCmrSha.
Import ListNotations.

(* list N (bytes 0..255) -> CmrBits, using the decoder's own bit order. *)
Definition cmrbits_of_bytes (bs : list N) : CmrBits :=
  bytes_to_bits (map N.to_nat bs).

(* Inverse: 8 MSB-first bits -> one byte. *)
Definition byte_of_bits8 (bits : list bool) : N :=
  fold_left (fun acc (b : bool) => N.add (N.mul 2 acc) (if b then 1%N else 0%N)) bits 0%N.

Fixpoint bytes_of_bits (bits : list bool) : list N :=
  match bits with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      byte_of_bits8 [b0; b1; b2; b3; b4; b5; b6; b7] :: bytes_of_bits rest
  | _ => []
  end.

(* The conversions round-trip on real 32-byte CMR data. *)
Example bytes_bits_roundtrip_unit : bytes_of_bits (cmrbits_of_bytes UNIT_IV) = UNIT_IV.
Proof. vm_compute. reflexivity. Qed.

Example bytes_bits_roundtrip_bits0 : bytes_of_bits (cmrbits_of_bytes BITS0) = BITS0.
Proof. vm_compute. reflexivity. Qed.

(* The concrete SHA-256-backed Simplicity CMR algebra. *)
Definition simplicity_cmr_algebra : CmrAlgebra :=
  {| cmr_iden := cmrbits_of_bytes IDEN_IV
   ; cmr_unit := cmrbits_of_bytes UNIT_IV
   ; cmr_injl := fun c => cmrbits_of_bytes (scmr_injl (bytes_of_bits c))
   ; cmr_injr := fun c => cmrbits_of_bytes (scmr_injr (bytes_of_bits c))
   ; cmr_take := fun c => cmrbits_of_bytes (scmr_take (bytes_of_bits c))
   ; cmr_drop := fun c => cmrbits_of_bytes (scmr_drop (bytes_of_bits c))
   ; cmr_comp := fun l r => cmrbits_of_bytes (scmr_comp (bytes_of_bits l) (bytes_of_bits r))
   ; cmr_case := fun l r => cmrbits_of_bytes (scmr_case (bytes_of_bits l) (bytes_of_bits r))
   ; cmr_pair := fun l r => cmrbits_of_bytes (scmr_pair (bytes_of_bits l) (bytes_of_bits r))
   ; cmr_disconnect := fun c => cmrbits_of_bytes (scmr_disconnect (bytes_of_bits c))
   ; cmr_witness := cmrbits_of_bytes WITNESS_IV
   ; cmr_fail := fun eb =>
       let b := bytes_of_bits eb in
       cmrbits_of_bytes (scmr_fail (firstn 32 b) (skipn 32 b))
   ; cmr_jet := fun j => elements_jet_cmr_bits j
   ; cmr_word := fun ew vb => cmrbits_of_bytes (cmr_word_bytes ew vb)
  |}.
