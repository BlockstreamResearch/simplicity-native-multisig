(*
  CompiledMultisigRealCmr.v — Step 6/7 of G5 Route B: the strongest byte-level
  artifact proof for the CMR, with NO exporter or foundation trust.

  `compiled_multisig_streaming_structural_program` is the streaming Coq byte
  decoder applied to the deployed certificate's `cert_program_bytes`.  This file
  proves that the REAL SHA-256 commitment Merkle root of that decoded program,
  computed by the self-contained `simplicity_cmr_algebra` (Sha256Core.v +
  SimplicityCmrSha.v), equals the exported `cert_cmr_bytes` — and that every jet
  in the program is in the multisig whitelist.

  Unlike every prior CMR theorem in the tree, this is UNCONDITIONAL: it does not
  assume a `... = Some program` premise and does not quantify over an abstract
  CmrAlgebra.  The commitment value is recomputed from first principles (a
  vetted SHA-256, validated against FIPS 180-4 and against rust-simplicity's
  BITS = injl/injr(unit)) and matched against the deployed 32 bytes by
  computation.  `Print Assumptions` reports "Closed under the global context".
*)

From Coq Require Import List.
From MultisigFormal Require Import
  CompiledMultisigExampleCore
  SimplicityByteDecoderCmrCore
  SimplicityByteDecoderProgramTypes
  SimplicityCmrAlgebra
  MultisigCertificateCore
  CompiledMultisigByteData.

(* The closed computation: decode the deployed bytes and recompute the root CMR
   under the concrete SHA-256 algebra; it equals the exported CMR bits. *)
Lemma compiled_multisig_streaming_real_cmr_closed :
  option_map (compute_structural_program_cmr simplicity_cmr_algebra)
             compiled_multisig_streaming_structural_program
  = Some (Some (certificate_cmr_bits compiled_multisig_certificate)).
Proof. lazy. reflexivity. Qed.

(* The deployed byte artifact decodes to a program whose real commitment Merkle
   root is exactly the exported CMR, and every jet is whitelisted. *)
Theorem compiled_multisig_real_cmr_matches_exported :
  exists program,
    compiled_multisig_streaming_structural_program = Some program /\
    compute_structural_program_cmr simplicity_cmr_algebra program
      = Some (certificate_cmr_bits compiled_multisig_certificate) /\
    structural_program_uses_only_multisig_jets program.
Proof.
  destruct compiled_multisig_streaming_structural_program_exists as [program Hprog].
  exists program. split; [exact Hprog | split].
  - pose proof compiled_multisig_streaming_real_cmr_closed as H.
    rewrite Hprog in H. cbn in H. injection H as H. exact H.
  - apply structural_program_jets_are_multisig_subset.
Qed.
