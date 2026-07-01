From Coq Require Import Bool.
From MultisigFormal Require Import
  CmrWellFormed CompiledMultisigByteData CompiledMultisigExample
  CompiledMultisigTypedExample FoundationCore FoundationElementsProviders
  MultisigCertificate MultisigTypedCertificate SimplicityByteDecoder
  TypedBridge.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Concrete compiled-artifact foundation bridge.

  FoundationCore.v proves the generic typed-byte root construction theorem.
  This module applies that theorem to the actual generated multisig typed byte
  certificate.  The only remaining term-construction input is the explicit
  non-core primitive provider family for assertions, jets, witnesses, words,
  and disconnect nodes.
*)

Theorem compiled_multisig_streaming_typed_root_foundation_term :
  forall program,
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    foundation_non_core_term_provider_for_prefixes
      (typed_certificate_hooks reject_unhandled_type_hooks) ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros program Hdecoded Hnon_core.
  pose proof
    (@compiled_multisig_streaming_typed_decode_evidence_if_checked
      program
      Hdecoded) as Hcompact.
  destruct Hcompact as [[typed_certificate [Hexpanded Htyped_decode]]].
  destruct Htyped_decode as [_ Htyped_byte].
  assert
    (Hcompiled_typed :
      compiled_multisig_typed_certificate = Some typed_certificate).
  {
    unfold compiled_multisig_typed_certificate.
    exact Hexpanded.
  }
  pose proof
    (@compiled_multisig_typed_certificate_atom_free
      typed_certificate
      Hcompiled_typed) as Hatom_free.
  unfold typed_byte_certificate_atom_free in Hatom_free.
  apply andb_true_iff in Hatom_free as [Htypes_atom_free _].
  destruct
    (@typed_byte_root_foundation_term_from_recursive_evidence
      (typed_certificate_hooks reject_unhandled_type_hooks)
      program
      (typed_certificate_types typed_certificate)
      (typed_certificate_root_arrow typed_certificate)
      Htyped_byte
      Htypes_atom_free
      Hnon_core)
    as [foundation_term Hfoundation_term].
  exists typed_certificate.
  split.
  - exact Hcompiled_typed.
  - exists foundation_term.
    exact Hfoundation_term.
Qed.

Theorem compiled_multisig_streaming_typed_root_foundation_term_exists :
  foundation_non_core_term_provider_for_prefixes
    (typed_certificate_hooks reject_unhandled_type_hooks) ->
  exists program typed_certificate,
    compiled_multisig_streaming_typed_decoded_program = Some program /\
    compiled_multisig_typed_certificate = Some typed_certificate /\
    exists foundation_term :
      FoundationTermForArrow
        (typed_certificate_root_arrow typed_certificate),
      True.
Proof.
  intros Hnon_core.
  destruct compiled_multisig_streaming_typed_decode_evidence
    as [program [Hdecoded _]].
  destruct
    (@compiled_multisig_streaming_typed_root_foundation_term
      program
      Hdecoded
      Hnon_core)
    as [typed_certificate [Htyped_certificate Hfoundation_term]].
  exists program, typed_certificate.
  split.
  - exact Hdecoded.
  - split.
    + exact Htyped_certificate.
       + exact Hfoundation_term.
Qed.

Theorem compiled_multisig_streaming_typed_root_foundation_term_with_elements_providers :
  forall program,
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    foundation_elements_term_provider_for_prefixes
      reject_unhandled_type_hooks ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros program Hdecoded Hproviders.
  eapply compiled_multisig_streaming_typed_root_foundation_term.
  - exact Hdecoded.
  - eapply foundation_non_core_term_provider_for_prefixes_from_elements_providers.
    exact Hproviders.
Qed.

Theorem compiled_multisig_streaming_typed_root_foundation_term_exists_with_elements_providers :
  foundation_elements_term_provider_for_prefixes
    reject_unhandled_type_hooks ->
  exists program typed_certificate,
    compiled_multisig_streaming_typed_decoded_program = Some program /\
    compiled_multisig_typed_certificate = Some typed_certificate /\
    exists foundation_term :
      FoundationTermForArrow
        (typed_certificate_root_arrow typed_certificate),
      True.
Proof.
  intros Hproviders.
  eapply compiled_multisig_streaming_typed_root_foundation_term_exists.
  eapply foundation_non_core_term_provider_for_prefixes_from_elements_providers.
  exact Hproviders.
Qed.

Theorem compiled_multisig_typed_bridge_root_foundation_term :
  forall alg program,
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg
      reject_unhandled_type_hooks
      compiled_multisig_compact_typed_certificate
      program ->
    foundation_non_core_term_provider_for_prefixes
      (typed_certificate_hooks reject_unhandled_type_hooks) ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros alg program Hbridge Hnon_core.
  destruct Hbridge as [[typed_certificate [Hexpanded Htyped_bridge]]].
  destruct Htyped_bridge as [_ Htyped_byte].
  assert
    (Hcompiled_typed :
      compiled_multisig_typed_certificate = Some typed_certificate).
  {
    unfold compiled_multisig_typed_certificate.
    exact Hexpanded.
  }
  pose proof
    (@compiled_multisig_typed_certificate_atom_free
      typed_certificate
      Hcompiled_typed) as Hatom_free.
  unfold typed_byte_certificate_atom_free in Hatom_free.
  apply andb_true_iff in Hatom_free as [Htypes_atom_free _].
  destruct
    (@typed_byte_root_foundation_term_from_recursive_evidence
      (typed_certificate_hooks reject_unhandled_type_hooks)
      program
      (typed_certificate_types typed_certificate)
      (typed_certificate_root_arrow typed_certificate)
      Htyped_byte
      Htypes_atom_free
      Hnon_core)
    as [foundation_term Hfoundation_term].
  exists typed_certificate.
  split.
  - exact Hcompiled_typed.
  - exists foundation_term.
    exact Hfoundation_term.
Qed.

Theorem compiled_multisig_typed_bridge_root_foundation_term_with_elements_providers :
  forall alg program,
    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence
      alg
      reject_unhandled_type_hooks
      compiled_multisig_compact_typed_certificate
      program ->
    foundation_elements_term_provider_for_prefixes
      reject_unhandled_type_hooks ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros alg program Hbridge Hproviders.
  eapply compiled_multisig_typed_bridge_root_foundation_term.
  - exact Hbridge.
  - eapply foundation_non_core_term_provider_for_prefixes_from_elements_providers.
    exact Hproviders.
Qed.

Local Opaque compiled_multisig_certificate.
Local Opaque compiled_multisig_compact_typed_certificate.
Local Opaque compiled_multisig_typed_certificate.
Local Opaque compiled_multisig_streaming_typed_decoded_program.
Local Opaque compiled_multisig_streaming_typed_checked_program.

Theorem compiled_multisig_streaming_typed_cmr_checked_root_foundation_term :
  forall alg program,
    CmrAlgebraWellFormed alg ->
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits compiled_multisig_certificate) ->
    foundation_non_core_term_provider_for_prefixes
      (typed_certificate_hooks reject_unhandled_type_hooks) ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros alg program Halg Hdecoded Hcmr Hnon_core.
  pose proof
    (@compiled_multisig_streaming_typed_bridge_evidence_from_cmr_if_checked
      alg
      program
      Halg
      Hdecoded
      Hcmr) as Hbridge.
  exact
    (@compiled_multisig_typed_bridge_root_foundation_term
      alg
      program
      Hbridge
      Hnon_core).
Qed.

Theorem compiled_multisig_streaming_typed_checked_root_foundation_term :
  forall alg program,
    compiled_multisig_streaming_typed_checked_program
      alg reject_unhandled_type_hooks = Some program ->
    foundation_non_core_term_provider_for_prefixes
      (typed_certificate_hooks reject_unhandled_type_hooks) ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros alg program Hchecked Hnon_core.
  pose proof
    (@compiled_multisig_streaming_typed_bridge_evidence_if_checked
      alg
      reject_unhandled_type_hooks
      program
      Hchecked) as Hbridge.
  exact
    (@compiled_multisig_typed_bridge_root_foundation_term
      alg
      program
      Hbridge
      Hnon_core).
Qed.

Theorem compiled_multisig_streaming_typed_checked_root_foundation_term_with_elements_providers :
  forall alg program,
    compiled_multisig_streaming_typed_checked_program
      alg reject_unhandled_type_hooks = Some program ->
    foundation_elements_term_provider_for_prefixes
      reject_unhandled_type_hooks ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True.
Proof.
  intros alg program Hchecked Hproviders.
  eapply compiled_multisig_streaming_typed_checked_root_foundation_term.
  - exact Hchecked.
  - eapply foundation_non_core_term_provider_for_prefixes_from_elements_providers.
    exact Hproviders.
Qed.
