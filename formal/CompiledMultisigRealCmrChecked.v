(*
  CompiledMultisigRealCmrChecked.v — G5 polish: lift the real-CMR result to the
  decoder's CHECKED CMR path under the concrete `simplicity_cmr_algebra`.

  This reuses the (heavy) `compiled_multisig_real_cmr_matches_exported` result and
  the well-formedness of the algebra to discharge the checked CMR computation
  WITHOUT recomputing SHA-256 over the program: by
  `compute_structural_program_cmr_checked_matches_unchecked`, a well-formed
  algebra with 256-bit hidden CMRs makes the checked pass agree with the ordinary
  pass.  The result is the first UNCONDITIONAL checked-CMR fact in the tree tied
  to a real SHA-256 algebra and the deployed artifact.
*)

From Coq Require Import List.
From MultisigFormal Require Import
  CompiledMultisigExampleCore CompiledMultisigRealCmr
  SimplicityCmrAlgebra SimplicityCmrAlgebraWf
  CmrWellFormed SimplicityByteDecoderCmrCore SimplicityByteDecoderProgramTypes
  SimplicityByteDecoder
  MultisigCertificateCore CompiledMultisigByteData.

Theorem compiled_multisig_real_checked_cmr :
  exists program,
    compiled_multisig_streaming_structural_program = Some program /\
    compute_structural_program_cmr_checked simplicity_cmr_algebra program
      = Some (certificate_cmr_bits compiled_multisig_certificate).
Proof.
  destruct compiled_multisig_real_cmr_matches_exported as [program [Hdec [Hcmr _Hjets]]].
  exists program. split; [exact Hdec |].
  apply compute_structural_program_cmr_checked_matches_unchecked.
  - exact simplicity_cmr_algebra_well_formed.
  - eapply decode_structural_program_bytes_streaming_hidden_cmrs_256.
    unfold compiled_multisig_streaming_structural_program in Hdec. exact Hdec.
  - exact Hcmr.
Qed.
