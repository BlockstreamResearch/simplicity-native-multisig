Require Import Simplicity.Core.
Require Import Simplicity.Ty.
From Coq Require Import Bool List.
From MultisigFormal Require Import
  FoundationCoreTerms FoundationCoreTypes SimplicityByteDecoder TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma forallb_option_bridge_arrow_atom_free_nth_error :
  forall types index arrow,
    forallb option_bridge_arrow_atom_free types = true ->
    nth_error types index = Some (Some arrow) ->
    bridge_arrow_atom_free arrow = true.
Proof.
  induction types as [| entry rest IH];
    intros index arrow Hall Hnth.
  - destruct index; discriminate.
  - simpl in Hall.
    apply andb_true_iff in Hall as [Hentry Hrest].
    destruct index as [| index'].
    + simpl in Hnth.
      destruct entry as [head_arrow |]; [| discriminate].
      inversion Hnth; subst head_arrow.
      exact Hentry.
    + simpl in Hnth.
      eapply IH; eauto.
Qed.

Theorem foundation_child_term_provider_from_typed_nodes :
  forall hooks nodes types prefix,
    typed_nodes_type_evidence_from hooks prefix nodes types ->
    forallb option_bridge_arrow_atom_free types = true ->
    foundation_child_term_provider prefix ->
    foundation_non_core_term_provider_for_prefixes hooks ->
    exists provider : foundation_child_term_provider (prefix ++ types), True.
Proof.
  intros hooks nodes.
  induction nodes as [| node_entry rest_nodes IH];
    intros types prefix Hevidence Hatom_free_table Hchildren Hnon_core.
  - destruct types as [| type_entry rest_types].
    + rewrite app_nil_r.
      exists Hchildren.
      exact I.
    + simpl in Hevidence.
      exact (False_rect _ Hevidence).
  - destruct types as [| type_entry rest_types].
    + simpl in Hevidence.
      destruct node_entry; exact (False_rect _ Hevidence).
    + destruct node_entry as [node | hidden_cmr].
      * destruct type_entry as [arrow |].
        -- simpl in Hevidence.
           destruct Hevidence as [Hnode_evidence Hrest_evidence].
           simpl in Hatom_free_table.
           apply andb_true_iff in Hatom_free_table
             as [Harrow_atom_free Hrest_atom_free].
           destruct
             (@foundation_term_from_type_evidence_with_non_core
               hooks
               prefix
               node
               arrow
               Harrow_atom_free
               Hnode_evidence
               Hchildren
               (Hnon_core prefix))
             as [foundation_term _].
           destruct
             (IH
               rest_types
               (prefix ++ [Some arrow])
               Hrest_evidence
               Hrest_atom_free
               (@extend_foundation_child_term_provider_some
                 prefix arrow Hchildren foundation_term)
               Hnon_core)
             as [provider _].
           replace (prefix ++ Some arrow :: rest_types)
             with ((prefix ++ [Some arrow]) ++ rest_types)
             by (rewrite <- app_assoc; reflexivity).
           exists provider.
           exact I.
        -- simpl in Hevidence.
           exact (False_rect _ Hevidence).
      * destruct type_entry as [arrow |].
        -- simpl in Hevidence.
           exact (False_rect _ Hevidence).
        -- simpl in Hatom_free_table.
           destruct
             (IH
               rest_types
               (prefix ++ [None])
               Hevidence
               Hatom_free_table
               (@extend_foundation_child_term_provider_none
                 prefix Hchildren)
               Hnon_core)
             as [provider _].
           replace (prefix ++ None :: rest_types)
             with ((prefix ++ [None]) ++ rest_types)
             by (rewrite <- app_assoc; reflexivity).
           exists provider.
           exact I.
Qed.

Theorem typed_program_child_terms_from_type_evidence :
  forall hooks program types root_arrow,
    TypedStructuralProgramEvidence hooks program types root_arrow ->
    forallb option_bridge_arrow_atom_free types = true ->
    foundation_non_core_term_provider_for_prefixes hooks ->
    exists provider : foundation_child_term_provider types, True.
Proof.
  intros hooks program types root_arrow
    Htyped Hatom_free_table Hnon_core.
  pose proof (typed_node_type_evidence Htyped) as Hevidence.
  unfold typed_program_nodes_have_type_evidence in Hevidence.
  destruct
    (@foundation_child_term_provider_from_typed_nodes
      hooks
      (structural_nodes program)
      types
      []
      Hevidence
      Hatom_free_table
      empty_foundation_child_term_provider
      Hnon_core)
    as [provider _].
  simpl in provider.
  exists provider.
  exact I.
Qed.

Theorem typed_program_node_foundation_term_from_type_evidence :
  forall hooks program types root_arrow index node arrow,
    TypedStructuralProgramEvidence hooks program types root_arrow ->
    forallb option_bridge_arrow_atom_free types = true ->
    nth_error (structural_nodes program) index = Some (CNode node) ->
    nth_error types index = Some (Some arrow) ->
    foundation_child_term_provider (firstn index types) ->
    foundation_non_core_term_provider hooks (firstn index types) ->
    exists foundation_term : FoundationTermForArrow arrow, True.
Proof.
  intros hooks program types root_arrow index node arrow
    Htyped Hatom_free_table Hnode Htype Hchildren Hnon_core.
  pose proof
    (@typed_program_node_has_type_evidence
      hooks program types root_arrow index node arrow
      Htyped Hnode Htype) as Hevidence.
  pose proof
    (@forallb_option_bridge_arrow_atom_free_nth_error
      types index arrow Hatom_free_table Htype) as Hatom_free.
  eapply foundation_term_from_type_evidence_with_non_core; eauto.
Qed.

Theorem typed_program_root_foundation_term_from_recursive_evidence :
  forall hooks program types root_arrow,
    TypedStructuralProgramEvidence hooks program types root_arrow ->
    structural_program_dag_well_formed program = true ->
    forallb option_bridge_arrow_atom_free types = true ->
    foundation_non_core_term_provider_for_prefixes hooks ->
    exists foundation_term : FoundationTermForArrow root_arrow, True.
Proof.
  intros hooks program types root_arrow Htyped Hdag
    Hatom_free_table Hnon_core.
  pose proof
    (@typed_root_entry_has_arrow
      program
      types
      root_arrow
      Hdag
      (typed_root_checked Htyped))
    as Hroot_arrow.
  destruct Hroot_arrow as [root_node [Hroot_node Hroot_type]].
  destruct
    (@typed_program_child_terms_from_type_evidence
      hooks
      program
      types
      root_arrow
      Htyped
      Hatom_free_table
      Hnon_core)
    as [all_children _].
  pose proof all_children as root_children.
  rewrite <- (firstn_skipn (structural_root program) types) in root_children.
  pose
    (restricted_children :=
      @restrict_foundation_child_term_provider
        (firstn (structural_root program) types)
        (skipn (structural_root program) types)
        root_children).
  eapply typed_program_node_foundation_term_from_type_evidence.
  - exact Htyped.
  - exact Hatom_free_table.
  - exact Hroot_node.
  - exact Hroot_type.
  - exact restricted_children.
  - exact (Hnon_core (firstn (structural_root program) types)).
Qed.

Theorem typed_byte_node_foundation_term_from_evidence :
  forall hooks program types root_arrow index node arrow,
    TypedByteBridgeEvidence hooks program types root_arrow ->
    forallb option_bridge_arrow_atom_free types = true ->
    nth_error (structural_nodes program) index = Some (CNode node) ->
    nth_error types index = Some (Some arrow) ->
    foundation_child_term_provider (firstn index types) ->
    foundation_non_core_term_provider hooks (firstn index types) ->
    exists foundation_term : FoundationTermForArrow arrow, True.
Proof.
  intros hooks program types root_arrow index node arrow
    Htyped Hatom_free_table Hnode Htype Hchildren Hnon_core.
  eapply typed_program_node_foundation_term_from_type_evidence.
  - exact (typed_byte_program Htyped).
  - exact Hatom_free_table.
  - exact Hnode.
  - exact Htype.
  - exact Hchildren.
  - exact Hnon_core.
Qed.

Theorem typed_byte_root_foundation_term_from_recursive_evidence :
  forall hooks program types root_arrow,
    TypedByteBridgeEvidence hooks program types root_arrow ->
    forallb option_bridge_arrow_atom_free types = true ->
    foundation_non_core_term_provider_for_prefixes hooks ->
    exists foundation_term : FoundationTermForArrow root_arrow, True.
Proof.
  intros hooks program types root_arrow
    Htyped Hatom_free_table Hnon_core.
  eapply typed_program_root_foundation_term_from_recursive_evidence.
  - exact (typed_byte_program Htyped).
  - exact (typed_byte_dag Htyped).
  - exact Hatom_free_table.
  - exact Hnon_core.
Qed.

Theorem typed_byte_root_foundation_term_from_evidence :
  forall hooks program types root_arrow,
    TypedByteBridgeEvidence hooks program types root_arrow ->
    forallb option_bridge_arrow_atom_free types = true ->
    foundation_child_term_provider
      (firstn (structural_root program) types) ->
    foundation_non_core_term_provider
      hooks
      (firstn (structural_root program) types) ->
    exists foundation_term : FoundationTermForArrow root_arrow, True.
Proof.
  intros hooks program types root_arrow Htyped Hatom_free_table
    Hchildren Hnon_core.
  destruct (typed_byte_root_arrow Htyped)
    as [root_node [Hroot_node Hroot_type]].
  eapply typed_byte_node_foundation_term_from_evidence.
  - exact Htyped.
  - exact Hatom_free_table.
  - exact Hroot_node.
  - exact Hroot_type.
  - exact Hchildren.
  - exact Hnon_core.
Qed.
