From Coq Require Import Bool.
From MultisigFormal Require Import
  ElementsJetTypes FoundationCore MultisigTypedCertificate
  SimplicityByteDecoder TypedBridge.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Contract-facing non-core provider interface.

  FoundationCore.v packages compiled root-term construction behind a generic
  non-core provider.  This module narrows that obligation for the multisig
  typed-certificate hook profile: callers must supply providers only for the
  non-core node families that the no-witness artifact can legitimately contain.
  Fail nodes and reserved one-child disconnect nodes are rejected by the typed
  certificate hooks, so their cases are discharged here rather than exposed as
  provider obligations.
*)

Record FoundationElementsTermProviders
    (base_hooks : TypeHooks)
    (prefix : list (option BridgeArrow)) : Type := {
  foundation_elements_assertl_provider :
    forall lhs hidden_cmr_bits arrow,
      bridge_arrow_atom_free arrow = true ->
      structural_node_type_evidence
        (typed_certificate_hooks base_hooks)
        prefix
        (SAssertL lhs hidden_cmr_bits)
        arrow ->
      foundation_child_term_provider prefix ->
      exists foundation_term : FoundationTermForArrow arrow, True;
  foundation_elements_assertr_provider :
    forall hidden_cmr_bits rhs arrow,
      bridge_arrow_atom_free arrow = true ->
      structural_node_type_evidence
        (typed_certificate_hooks base_hooks)
        prefix
        (SAssertR hidden_cmr_bits rhs)
        arrow ->
      foundation_child_term_provider prefix ->
      exists foundation_term : FoundationTermForArrow arrow, True;
  foundation_elements_disconnect_provider :
    forall lhs rhs arrow,
      bridge_arrow_atom_free arrow = true ->
      structural_node_type_evidence
        (typed_certificate_hooks base_hooks)
        prefix
        (SDisconnect lhs rhs)
        arrow ->
      foundation_child_term_provider prefix ->
      exists foundation_term : FoundationTermForArrow arrow, True;
  foundation_elements_witness_provider :
    forall arrow,
      bridge_arrow_atom_free arrow = true ->
      structural_node_type_evidence
        (typed_certificate_hooks base_hooks)
        prefix
        SWitness
        arrow ->
      foundation_child_term_provider prefix ->
      exists foundation_term : FoundationTermForArrow arrow, True;
  foundation_elements_jet_provider :
    forall jet arrow,
      bridge_arrow_atom_free arrow = true ->
      structural_node_type_evidence
        (typed_certificate_hooks base_hooks)
        prefix
        (SJet jet)
        arrow ->
      foundation_child_term_provider prefix ->
      exists foundation_term : FoundationTermForArrow arrow, True;
  foundation_elements_word_provider :
    forall encoded_width value_bits arrow,
      bridge_arrow_atom_free arrow = true ->
      structural_node_type_evidence
        (typed_certificate_hooks base_hooks)
        prefix
        (SWord encoded_width value_bits)
        arrow ->
      foundation_child_term_provider prefix ->
      exists foundation_term : FoundationTermForArrow arrow, True
}.

Definition foundation_elements_term_provider_for_prefixes
    (base_hooks : TypeHooks) : Type :=
  forall prefix, FoundationElementsTermProviders base_hooks prefix.

Lemma typed_certificate_hooks_disconnect1_rejects :
  forall base_hooks prefix lhs arrow,
    structural_node_type_evidence
      (typed_certificate_hooks base_hooks)
      prefix
      (SDisconnect1 lhs)
      arrow ->
    False.
Proof.
  intros base_hooks prefix lhs arrow Hevidence.
  simpl in Hevidence.
  destruct Hevidence as [lhs_arrow [_ Hallowed]].
  unfold typed_certificate_hooks in Hallowed.
  simpl in Hallowed.
  discriminate Hallowed.
Qed.

Lemma typed_certificate_hooks_fail_rejects :
  forall base_hooks prefix entropy_bits arrow,
    structural_node_type_evidence
      (typed_certificate_hooks base_hooks)
      prefix
      (SFail entropy_bits)
      arrow ->
    False.
Proof.
  intros base_hooks prefix entropy_bits arrow Hevidence.
  unfold typed_certificate_hooks in Hevidence.
  simpl in Hevidence.
  discriminate Hevidence.
Qed.

Theorem foundation_non_core_term_provider_from_elements_providers :
  forall base_hooks prefix,
    FoundationElementsTermProviders base_hooks prefix ->
    foundation_non_core_term_provider
      (typed_certificate_hooks base_hooks)
      prefix.
Proof.
  intros base_hooks prefix Hproviders node arrow
    Hnon_core Hatom_free Hevidence Hchildren.
  destruct Hproviders as
    [Hassertl Hassertr Hdisconnect Hwitness Hjet Hword].
  destruct node as
    [| | child | child | child | child | lhs rhs | lhs rhs
     | lhs hidden_cmr_bits | hidden_cmr_bits rhs | lhs rhs
     | lhs | lhs rhs | | entropy_bits | jet | encoded_width value_bits];
    simpl in Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - discriminate Hnon_core.
  - exact (Hassertl lhs hidden_cmr_bits arrow Hatom_free Hevidence Hchildren).
  - exact (Hassertr hidden_cmr_bits rhs arrow Hatom_free Hevidence Hchildren).
  - discriminate Hnon_core.
  - exfalso.
    eapply typed_certificate_hooks_disconnect1_rejects.
    exact Hevidence.
  - exact (Hdisconnect lhs rhs arrow Hatom_free Hevidence Hchildren).
  - exact (Hwitness arrow Hatom_free Hevidence Hchildren).
  - exfalso.
    eapply typed_certificate_hooks_fail_rejects.
    exact Hevidence.
  - exact (Hjet jet arrow Hatom_free Hevidence Hchildren).
  - exact (Hword encoded_width value_bits arrow Hatom_free Hevidence Hchildren).
Qed.

Theorem foundation_non_core_term_provider_for_prefixes_from_elements_providers :
  forall base_hooks,
    foundation_elements_term_provider_for_prefixes base_hooks ->
    foundation_non_core_term_provider_for_prefixes
      (typed_certificate_hooks base_hooks).
Proof.
  intros base_hooks Hproviders prefix.
  eapply foundation_non_core_term_provider_from_elements_providers.
  exact (Hproviders prefix).
Qed.
