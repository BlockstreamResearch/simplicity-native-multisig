From MultisigFormal Require Import
  CompiledMultisigByteData CompiledMultisigTypedExample FoundationCmrAlgebra
  MultisigCertificate MultisigTypedCertificateExamples SimplicityByteDecoder.

(*
  Byte-level projections specialized to the foundation-shaped CMR adapter.

  These theorems keep the artifact evidence path separate from the heavier
  model-security composition.  Once FoundationCmrOps is instantiated from the
  upstream Simplicity Digest/MerkleRoot implementation, these are the direct
  byte-decoder facts supplied by a successful checked run.

  PROOF-STYLE CONSTRAINT (memory): this file must NOT enable
  [Set Implicit Arguments]/[Set Strict Implicit], must state the shared decode
  fact as an opaque [Lemma] (not a transparent [Definition]), and must
  materialize applied lemmas with [pose proof ... as H] before [exact H].
  With the implicit-argument flags on, Qed-time kernel checking of these
  one-line proofs loses sharing on the statement types, unfolds
  [decode_structural_program_bytes_streaming] on the concrete certificate
  bytes, and re-runs the whole byte decoder inside the kernel: >26 GB RSS and
  ~30 GB of swap PER THEOREM (the single dominant memory cost of the build,
  and the trigger of the historical 250 GB parallel-build crash).  With the
  flags off the same proofs check in milliseconds at ~26 MB.
*)

Local Lemma compiled_multisig_foundation_cmr_checked_decode :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    decode_structural_program_bytes_streaming
      (cert_program_bytes compiled_multisig_certificate) =
      Some program.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_streaming_typed_checked_decoded_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks
      program
      Hchecked) as Hdecoded.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_decoded_program :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    decode_structural_program_bytes_streaming
      (cert_program_bytes compiled_multisig_certificate) =
      Some program.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops
      program
      Hchecked) as Hdecoded.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_cmr :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    compute_structural_program_cmr_checked
      (foundation_elements_cmr_algebra ops)
      program =
      Some (certificate_cmr_bits compiled_multisig_certificate).
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_streaming_typed_checked_cmr
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks
      program
      Hchecked) as Hcmr.
  exact Hcmr.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_hidden_cmrs_unique :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_hidden_cmrs_unique program.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_hidden_cmrs_unique.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_hidden_cmrs_256 :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_hidden_cmrs_256 program.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_hidden_cmrs_256.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_multisig_jet_subset :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_uses_only_multisig_jets program.
Proof.
  intros ops program _Hchecked.
  apply structural_program_jets_are_multisig_subset.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_dag_well_formed :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_dag_well_formed program = true.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_dag_well_formed.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_dag_len_bound :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    length (structural_nodes program) <= dag_len_max.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_dag_len_bound.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_child_references :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_child_references.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_no_fail :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_no_fail program = true.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_no_fail.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_no_disconnect1 :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_no_disconnect1.
  exact Hdecoded.
Qed.

Theorem compiled_multisig_foundation_cmr_checked_closed_padding :
  forall ops program,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
    program_bytes_streaming_closed_padding
      (cert_program_bytes compiled_multisig_certificate) = true.
Proof.
  intros ops program Hchecked.
  pose proof
    (@compiled_multisig_foundation_cmr_checked_decode
      ops program Hchecked) as Hdecoded.
  eapply decode_structural_program_bytes_streaming_closed_padding.
  exact Hdecoded.
Qed.
