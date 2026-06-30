Require Import Simplicity.Core.
Require Import Simplicity.Ty.
From Coq Require Import Bool List.
From MultisigFormal Require Import
  BridgeTypeTranslation FoundationTypes FoundationCoreTypes
  SimplicityByteDecoder TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Theorem foundation_core_term_from_type_evidence :
  forall hooks prefix node arrow,
    structural_node_core_constructible node = true ->
    bridge_arrow_atom_free arrow = true ->
    structural_node_type_evidence hooks prefix node arrow ->
    foundation_child_term_provider prefix ->
    exists foundation_term : FoundationTermForArrow arrow, True.
Proof.
  intros hooks prefix node arrow Hcore Hatom_free Hevidence child_term.
  destruct arrow as [source target].
  destruct node as
    [| | child | child | child | child | lhs rhs | lhs rhs
     | lhs hidden_cmr | hidden_cmr rhs | lhs rhs | lhs
     | lhs rhs | | entropy_bits | jet | encoded_width value_bits];
    simpl in Hcore; try discriminate; simpl in Hevidence.
  - subst target.
    unfold bridge_arrow_atom_free in Hatom_free.
    simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hsource _].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsource)
      as [translated_source Htranslated_source].
    refine (ex_intro _ {|
      foundation_term_source := translated_source;
      foundation_term_target := translated_source;
      foundation_term_translation := _;
      foundation_term_body := iden
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _);
      exact Htranslated_source.
  - subst target.
    unfold bridge_arrow_atom_free in Hatom_free.
    simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hsource _].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsource)
      as [translated_source Htranslated_source].
    refine (ex_intro _ {|
      foundation_term_source := translated_source;
      foundation_term_target := Unit;
      foundation_term_translation := _;
      foundation_term_body := unit
    |} I).
    + apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
      * exact Htranslated_source.
      * reflexivity.
  - destruct Hevidence as
      [sum_left [sum_right [Htarget Hchild]]].
    subst target.
    unfold bridge_arrow_atom_free in Hatom_free.
    simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hsource Hsum].
    apply andb_true_iff in Hsum as [Hsum_left Hsum_right].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsource)
      as [translated_source Htranslated_source].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsum_left)
      as [translated_left Htranslated_left].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsum_right)
      as [translated_right Htranslated_right].
    pose proof
      (child_term
        child
        {| bridge_source := source; bridge_target := sum_left |}
        Hchild)
      as child_foundation_term.
    pose
      (child_body :=
        @cast_foundation_term_for_arrow
          _
          translated_source
          translated_left
          (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _
          Htranslated_source Htranslated_left)
          child_foundation_term).
    refine (ex_intro _ {|
      foundation_term_source := translated_source;
      foundation_term_target := Sum translated_left translated_right;
      foundation_term_translation := _;
      foundation_term_body := injl child_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
    + exact Htranslated_source.
    + unfold translate_bridge_type_to_simplicity_ty.
      simpl.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_left.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_right.
      rewrite Htranslated_left, Htranslated_right.
      reflexivity.
  - destruct Hevidence as
      [sum_left [sum_right [Htarget Hchild]]].
    subst target.
    unfold bridge_arrow_atom_free in Hatom_free.
    simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hsource Hsum].
    apply andb_true_iff in Hsum as [Hsum_left Hsum_right].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsource)
      as [translated_source Htranslated_source].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsum_left)
      as [translated_left Htranslated_left].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hsum_right)
      as [translated_right Htranslated_right].
    pose proof
      (child_term
        child
        {| bridge_source := source; bridge_target := sum_right |}
        Hchild)
      as child_foundation_term.
    pose
      (child_body :=
        @cast_foundation_term_for_arrow
          _
          translated_source
          translated_right
          (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _
          Htranslated_source Htranslated_right)
          child_foundation_term).
    refine (ex_intro _ {|
      foundation_term_source := translated_source;
      foundation_term_target := Sum translated_left translated_right;
      foundation_term_translation := _;
      foundation_term_body := injr child_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
    + exact Htranslated_source.
    + unfold translate_bridge_type_to_simplicity_ty.
      simpl.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_left.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_right.
      rewrite Htranslated_left, Htranslated_right.
      reflexivity.
  - destruct Hevidence as
      [prod_left [prod_right [Hsource Hchild]]].
    subst source.
    unfold bridge_arrow_atom_free in Hatom_free.
    simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hprod Htarget].
    apply andb_true_iff in Hprod as [Hprod_left Hprod_right].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hprod_left)
      as [translated_left Htranslated_left].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hprod_right)
      as [translated_right Htranslated_right].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Htarget)
      as [translated_target Htranslated_target].
    pose proof
      (child_term
        child
        {| bridge_source := prod_left; bridge_target := target |}
        Hchild)
      as child_foundation_term.
    pose
      (child_body :=
        @cast_foundation_term_for_arrow
          _
          translated_left
          translated_target
          (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _
          Htranslated_left Htranslated_target)
          child_foundation_term).
    refine (ex_intro _ {|
      foundation_term_source := Prod translated_left translated_right;
      foundation_term_target := translated_target;
      foundation_term_translation := _;
      foundation_term_body := take child_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
    + unfold translate_bridge_type_to_simplicity_ty.
      simpl.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_left.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_right.
      rewrite Htranslated_left, Htranslated_right.
      reflexivity.
    + exact Htranslated_target.
  - destruct Hevidence as
      [prod_left [prod_right [Hsource Hchild]]].
    subst source.
    unfold bridge_arrow_atom_free in Hatom_free.
    simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hprod Htarget].
    apply andb_true_iff in Hprod as [Hprod_left Hprod_right].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hprod_left)
      as [translated_left Htranslated_left].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Hprod_right)
      as [translated_right Htranslated_right].
    destruct
      (translate_bridge_type_to_simplicity_ty_atom_free_sig _ Htarget)
      as [translated_target Htranslated_target].
    pose proof
      (child_term
        child
        {| bridge_source := prod_right; bridge_target := target |}
        Hchild)
      as child_foundation_term.
    pose
      (child_body :=
        @cast_foundation_term_for_arrow
          _
          translated_right
          translated_target
          (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _
          Htranslated_right Htranslated_target)
          child_foundation_term).
    refine (ex_intro _ {|
      foundation_term_source := Prod translated_left translated_right;
      foundation_term_target := translated_target;
      foundation_term_translation := _;
      foundation_term_body := drop child_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
    + unfold translate_bridge_type_to_simplicity_ty.
      simpl.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_left.
      unfold translate_bridge_type_to_simplicity_ty in Htranslated_right.
      rewrite Htranslated_left, Htranslated_right.
      reflexivity.
    + exact Htranslated_target.
  - destruct Hevidence as
      [lhs_arrow [rhs_arrow
       [Hlhs [Hrhs [Hlhs_source [Hmiddle Hrhs_target]]]]]].
    pose proof (child_term lhs lhs_arrow Hlhs) as lhs_foundation_term.
    pose proof (child_term rhs rhs_arrow Hrhs) as rhs_foundation_term.
    destruct lhs_arrow as [lhs_source lhs_target].
    destruct rhs_arrow as [rhs_source rhs_target].
    simpl in Hlhs_source, Hmiddle, Hrhs_target.
    subst lhs_source lhs_target rhs_target.
    destruct lhs_foundation_term as
      [translated_source translated_middle Hlhs_translate lhs_body].
    destruct rhs_foundation_term as
      [translated_middle' translated_target Hrhs_translate rhs_body].
    apply translate_bridge_arrow_to_simplicity_ty_elim
      in Hlhs_translate as [Htranslated_source Htranslated_middle].
    apply translate_bridge_arrow_to_simplicity_ty_elim
      in Hrhs_translate as [Htranslated_middle' Htranslated_target].
    simpl in Htranslated_middle, Htranslated_middle'.
    rewrite Htranslated_middle in Htranslated_middle'.
    inversion Htranslated_middle'; subst translated_middle'.
    refine (ex_intro _ {|
      foundation_term_source := translated_source;
      foundation_term_target := translated_target;
      foundation_term_translation := _;
      foundation_term_body := comp lhs_body rhs_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _);
      assumption.
  - destruct Hevidence as
      [sum_left [sum_right [ctx [Hsource [Hlhs Hrhs]]]]].
    subst source.
    pose proof
      (child_term
        lhs
        {| bridge_source := BTProd sum_left ctx;
           bridge_target := target |}
        Hlhs)
      as lhs_foundation_term.
    pose proof
      (child_term
        rhs
        {| bridge_source := BTProd sum_right ctx;
           bridge_target := target |}
        Hrhs)
      as rhs_foundation_term.
    destruct lhs_foundation_term as
      [translated_left_source translated_target Hlhs_translate lhs_body].
    destruct rhs_foundation_term as
      [translated_right_source translated_target' Hrhs_translate rhs_body].
    apply translate_bridge_arrow_to_simplicity_ty_elim
      in Hlhs_translate as [Hlhs_source Hlhs_target].
    apply translate_bridge_arrow_to_simplicity_ty_elim
      in Hrhs_translate as [Hrhs_source Hrhs_target].
    pose proof Hlhs_source as Hlhs_source_components.
    pose proof Hrhs_source as Hrhs_source_components.
    unfold translate_bridge_type_to_simplicity_ty
      in Hlhs_source_components, Hrhs_source_components.
    simpl in Hlhs_source_components, Hrhs_source_components.
    destruct (translate_bridge_type simplicity_ty_core_type_algebra sum_left)
      as [translated_left |] eqn:Htranslated_left; [| discriminate].
    destruct (translate_bridge_type simplicity_ty_core_type_algebra ctx)
      as [translated_ctx |] eqn:Htranslated_ctx; [| discriminate].
    inversion Hlhs_source_components; subst translated_left_source.
    destruct (translate_bridge_type simplicity_ty_core_type_algebra sum_right)
      as [translated_right |] eqn:Htranslated_right; [| discriminate].
    inversion Hrhs_source_components; subst translated_right_source.
    simpl in Hlhs_target, Hrhs_target.
    rewrite Hlhs_target in Hrhs_target.
    inversion Hrhs_target; subst translated_target'.
    refine (ex_intro _ {|
      foundation_term_source :=
        Prod (Sum translated_left translated_right) translated_ctx;
      foundation_term_target := translated_target;
      foundation_term_translation := _;
      foundation_term_body := case lhs_body rhs_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
    + unfold translate_bridge_type_to_simplicity_ty.
      simpl.
      rewrite Htranslated_left, Htranslated_right, Htranslated_ctx.
      reflexivity.
    + exact Hlhs_target.
  - destruct Hevidence as
      [prod_left [prod_right [Htarget [Hlhs Hrhs]]]].
    subst target.
    pose proof
      (child_term
        lhs
        {| bridge_source := source; bridge_target := prod_left |}
        Hlhs)
      as lhs_foundation_term.
    pose proof
      (child_term
        rhs
        {| bridge_source := source; bridge_target := prod_right |}
        Hrhs)
      as rhs_foundation_term.
    destruct lhs_foundation_term as
      [translated_source translated_left Hlhs_translate lhs_body].
    destruct rhs_foundation_term as
      [translated_source' translated_right Hrhs_translate rhs_body].
    apply translate_bridge_arrow_to_simplicity_ty_elim
      in Hlhs_translate as [Hlhs_source Hlhs_target].
    apply translate_bridge_arrow_to_simplicity_ty_elim
      in Hrhs_translate as [Hrhs_source Hrhs_target].
    simpl in Hlhs_source, Hrhs_source.
    rewrite Hlhs_source in Hrhs_source.
    inversion Hrhs_source; subst translated_source'.
    refine (ex_intro _ {|
      foundation_term_source := translated_source;
      foundation_term_target := Prod translated_left translated_right;
      foundation_term_translation := _;
      foundation_term_body := pair lhs_body rhs_body
    |} I).
    apply (@translate_bridge_arrow_to_simplicity_ty_intro _ _ _ _).
    + exact Hlhs_source.
    + unfold translate_bridge_type_to_simplicity_ty.
      simpl.
      simpl in Hlhs_target, Hrhs_target.
      unfold translate_bridge_type_to_simplicity_ty in Hlhs_target.
      unfold translate_bridge_type_to_simplicity_ty in Hrhs_target.
      rewrite Hlhs_target, Hrhs_target.
      reflexivity.
Qed.

Definition foundation_non_core_term_provider
    (hooks : TypeHooks)
    (prefix : list (option BridgeArrow)) : Type :=
  forall node arrow,
    structural_node_core_constructible node = false ->
    bridge_arrow_atom_free arrow = true ->
    structural_node_type_evidence hooks prefix node arrow ->
    foundation_child_term_provider prefix ->
    exists foundation_term : FoundationTermForArrow arrow, True.

Definition foundation_non_core_term_provider_for_prefixes
    (hooks : TypeHooks) : Type :=
  forall prefix,
    foundation_non_core_term_provider hooks prefix.

Theorem foundation_term_from_type_evidence_with_non_core :
  forall hooks prefix node arrow,
    bridge_arrow_atom_free arrow = true ->
    structural_node_type_evidence hooks prefix node arrow ->
    foundation_child_term_provider prefix ->
    foundation_non_core_term_provider hooks prefix ->
    exists foundation_term : FoundationTermForArrow arrow, True.
Proof.
  intros hooks prefix node arrow Hatom_free Hevidence Hchildren Hnon_core.
  destruct (structural_node_core_constructible node) eqn:Hcore.
  - eapply foundation_core_term_from_type_evidence; eauto.
  - eapply Hnon_core; eauto.
Qed.
