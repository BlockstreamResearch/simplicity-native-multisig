(*
  SimplicityCmrAlgebraWf.v — Step-4/G5 polish: the concrete SHA-256 CMR algebra
  is well-formed (every combinator outputs a 256-bit CmrBits).  This lets the
  decoder's CHECKED CMR path (compute_structural_program_cmr_checked, used by the
  certificate checkers) succeed under `simplicity_cmr_algebra`, via the existing
  compute_structural_program_cmr_checked_matches_unchecked bridge.

  Kept in a separate file so it does not invalidate the (heavy) .vo of
  CompiledMultisigRealCmr.v.
*)

From Coq Require Import NArith List.
From MultisigFormal Require Import
  SimplicityByteDecoderCmrCore SimplicityByteDecoderProgramTypes
  SimplicityByteDecoderBits MultisigCertificateCore
  ElementsJets ElementsJetCmr SimplicityCmrSha SimplicityCmrAlgebra CmrWellFormed.
Import ListNotations.

(* The bit image of a byte list is 8x as long (proved inline, no map_length dep). *)
Lemma cmrbits_of_bytes_length :
  forall bs, length (cmrbits_of_bytes bs) = 8 * length bs.
Proof.
  intros bs. unfold cmrbits_of_bytes. rewrite bytes_to_bits_length.
  f_equal. induction bs as [| x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma cmrbits_of_bytes_256 :
  forall bs, length bs = 32 -> cmr_bits_length_256 (cmrbits_of_bytes bs).
Proof.
  intros bs H. unfold cmr_bits_length_256.
  rewrite cmrbits_of_bytes_length, H. reflexivity.
Qed.

Theorem simplicity_cmr_algebra_well_formed :
  CmrAlgebraWellFormed simplicity_cmr_algebra.
Proof.
  constructor.
  - (* iden *) apply cmrbits_of_bytes_256; reflexivity.
  - (* unit *) apply cmrbits_of_bytes_256; reflexivity.
  - (* injl *) intros child; apply cmrbits_of_bytes_256; unfold scmr_injl; apply cmr_update1_length.
  - (* injr *) intros child; apply cmrbits_of_bytes_256; unfold scmr_injr; apply cmr_update1_length.
  - (* take *) intros child; apply cmrbits_of_bytes_256; unfold scmr_take; apply cmr_update1_length.
  - (* drop *) intros child; apply cmrbits_of_bytes_256; unfold scmr_drop; apply cmr_update1_length.
  - (* comp *) intros l r; apply cmrbits_of_bytes_256; unfold scmr_comp; apply cmr_update_length.
  - (* case *) intros l r; apply cmrbits_of_bytes_256; unfold scmr_case; apply cmr_update_length.
  - (* pair *) intros l r; apply cmrbits_of_bytes_256; unfold scmr_pair; apply cmr_update_length.
  - (* disconnect *) intros child; apply cmrbits_of_bytes_256; unfold scmr_disconnect; apply cmr_update1_length.
  - (* witness *) apply cmrbits_of_bytes_256; reflexivity.
  - (* fail *) intros eb; apply cmrbits_of_bytes_256; unfold scmr_fail; apply cmr_update_length.
  - (* jet *) intros jet; unfold cmr_bits_length_256; apply elements_jet_cmr_bits_length.
  - (* word *) intros ew vb; apply cmrbits_of_bytes_256; apply cmr_word_bytes_length.
Qed.
