Require Import Simplicity.Core.
Require Import Simplicity.Ty.
From Coq Require Import Bool List.
From MultisigFormal Require Import
  BridgeTypeTranslation FoundationTypes SimplicityByteDecoder TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Core-term adapter to the upstream Simplicity foundation.

  This module handles only the constructors present in Simplicity.Core.Term:
  iden, comp, unit, injl, injr, case, pair, take, and drop.  Assertions, jets,
  witnesses, words, and disconnect nodes need the heavier primitive/foundation
  semantics and remain outside this narrow adapter.
*)

Record FoundationTermForArrow (arrow : BridgeArrow) : Type := {
  foundation_term_source : Ty;
  foundation_term_target : Ty;
  foundation_term_translation :
    translate_bridge_arrow_to_simplicity_ty arrow =
      Some (foundation_term_source, foundation_term_target);
  foundation_term_body :
    Term foundation_term_source foundation_term_target
}.

Definition structural_node_core_constructible
    (node : StructuralNode) : bool :=
  match node with
  | SIden
  | SUnit
  | SInjL _
  | SInjR _
  | STake _
  | SDrop _
  | SComp _ _
  | SCase _ _
  | SPair _ _ => true
  | _ => false
  end.

Lemma translate_bridge_arrow_to_simplicity_ty_intro :
  forall source target translated_source translated_target,
    translate_bridge_type_to_simplicity_ty source = Some translated_source ->
    translate_bridge_type_to_simplicity_ty target = Some translated_target ->
    translate_bridge_arrow_to_simplicity_ty
      {| bridge_source := source; bridge_target := target |} =
      Some (translated_source, translated_target).
Proof.
  intros source target translated_source translated_target Hsource Htarget.
  unfold translate_bridge_arrow_to_simplicity_ty.
  unfold translate_bridge_arrow.
  simpl.
  unfold translate_bridge_type_to_simplicity_ty in Hsource, Htarget.
  rewrite Hsource, Htarget.
  reflexivity.
Qed.

Lemma translate_bridge_arrow_to_simplicity_ty_elim :
  forall arrow translated_source translated_target,
    translate_bridge_arrow_to_simplicity_ty arrow =
      Some (translated_source, translated_target) ->
    translate_bridge_type_to_simplicity_ty (bridge_source arrow) =
      Some translated_source /\
    translate_bridge_type_to_simplicity_ty (bridge_target arrow) =
      Some translated_target.
Proof.
  intros [source target] translated_source translated_target Htranslate.
  unfold translate_bridge_arrow_to_simplicity_ty in Htranslate.
  unfold translate_bridge_arrow in Htranslate.
  simpl in Htranslate.
  fold (translate_bridge_type_to_simplicity_ty source) in Htranslate.
  fold (translate_bridge_type_to_simplicity_ty target) in Htranslate.
  destruct (translate_bridge_type_to_simplicity_ty source)
    as [actual_source |] eqn:Hsource; [| discriminate].
  destruct (translate_bridge_type_to_simplicity_ty target)
    as [actual_target |] eqn:Htarget; [| discriminate].
  inversion Htranslate; subst actual_source actual_target.
  split; assumption.
Qed.

Definition translate_bridge_type_to_simplicity_ty_atom_free_sig
    (ty : BridgeType)
    (Hatom_free : bridge_type_atom_free ty = true) :
    { translated_type : Ty |
      translate_bridge_type_to_simplicity_ty ty = Some translated_type }.
Proof.
  destruct (translate_bridge_type_to_simplicity_ty ty)
    as [translated_type |] eqn:Htranslated.
  - exists translated_type. reflexivity.
  - exfalso.
    destruct
      (@translate_bridge_type_to_simplicity_ty_if_atom_free ty Hatom_free)
      as [translated_type Htranslated_type].
    rewrite Htranslated in Htranslated_type.
    discriminate.
Defined.

Definition cast_foundation_term_for_arrow
    (arrow : BridgeArrow)
    (source target : Ty)
    (Htranslate :
      translate_bridge_arrow_to_simplicity_ty arrow = Some (source, target))
    (term_for_arrow : FoundationTermForArrow arrow) :
    Term source target.
Proof.
  destruct term_for_arrow as
    [actual_source actual_target Hactual actual_term].
  rewrite Htranslate in Hactual.
  inversion Hactual; subst actual_source actual_target.
  exact actual_term.
Defined.

Definition foundation_child_term_provider
    (prefix : list (option BridgeArrow)) : Type :=
  forall child expected_arrow,
    child_has_arrow prefix child expected_arrow ->
    FoundationTermForArrow expected_arrow.

Definition empty_foundation_child_term_provider :
    foundation_child_term_provider [].
Proof.
  intros child expected_arrow Hchild.
  unfold child_has_arrow, typed_prefix_lookup in Hchild.
  destruct child; discriminate Hchild.
Defined.

Definition extend_foundation_child_term_provider_some
    (prefix : list (option BridgeArrow))
    (arrow : BridgeArrow)
    (provider : foundation_child_term_provider prefix)
    (term_for_arrow : FoundationTermForArrow arrow) :
    foundation_child_term_provider (prefix ++ [Some arrow]).
Proof.
  revert provider.
  induction prefix as [| entry rest IH];
    intros provider child expected_arrow Hchild.
  - destruct child as [| child'].
    + unfold child_has_arrow, typed_prefix_lookup in Hchild.
      simpl in Hchild.
      inversion Hchild; subst expected_arrow.
      exact term_for_arrow.
    + unfold child_has_arrow, typed_prefix_lookup in Hchild.
      destruct child'; discriminate Hchild.
  - destruct child as [| child'].
    + apply (provider 0 expected_arrow).
      unfold child_has_arrow, typed_prefix_lookup in *.
      simpl in *.
      exact Hchild.
    + apply
        (IH
          (fun tail_child tail_expected_arrow Htail =>
            provider (S tail_child) tail_expected_arrow Htail)
          child'
          expected_arrow).
      unfold child_has_arrow, typed_prefix_lookup in *.
      simpl in *.
      exact Hchild.
Defined.

Definition extend_foundation_child_term_provider_none
    (prefix : list (option BridgeArrow))
    (provider : foundation_child_term_provider prefix) :
    foundation_child_term_provider (prefix ++ [None]).
Proof.
  revert provider.
  induction prefix as [| entry rest IH];
    intros provider child expected_arrow Hchild.
  - unfold child_has_arrow, typed_prefix_lookup in Hchild.
    destruct child as [| [| child']]; simpl in Hchild; discriminate Hchild.
  - destruct child as [| child'].
    + apply (provider 0 expected_arrow).
      unfold child_has_arrow, typed_prefix_lookup in *.
      simpl in *.
      exact Hchild.
    + apply
        (IH
          (fun tail_child tail_expected_arrow Htail =>
            provider (S tail_child) tail_expected_arrow Htail)
          child'
          expected_arrow).
      unfold child_has_arrow, typed_prefix_lookup in *.
      simpl in *.
      exact Hchild.
Defined.

Definition restrict_foundation_child_term_provider
    (prefix suffix : list (option BridgeArrow))
    (provider : foundation_child_term_provider (prefix ++ suffix)) :
    foundation_child_term_provider prefix.
Proof.
  revert suffix provider.
  induction prefix as [| entry rest IH];
    intros suffix provider child expected_arrow Hchild.
  - unfold child_has_arrow, typed_prefix_lookup in Hchild.
    destruct child; discriminate Hchild.
  - destruct child as [| child'].
    + apply (provider 0 expected_arrow).
      unfold child_has_arrow, typed_prefix_lookup in *.
      simpl in *.
      exact Hchild.
    + apply
        (IH
          suffix
          (fun tail_child tail_expected_arrow Htail =>
            provider (S tail_child) tail_expected_arrow Htail)
          child'
          expected_arrow).
      unfold child_has_arrow, typed_prefix_lookup in *.
      simpl in *.
      exact Hchild.
Defined.

