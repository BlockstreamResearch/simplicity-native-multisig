From Coq Require Import List Bool.
From MultisigFormal Require Import MultisigTypedCertificate TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Foundation type-shape bridge.

  The upstream Simplicity foundation type language is Unit/Sum/Prod.  Our local
  BridgeType also has BTAtom as an escape hatch for future extension points.
  The compiled multisig artifact is already proved atom-free; this module makes
  the consequence executable and generic: any atom-free BridgeType table can be
  translated into any Unit/Sum/Prod type algebra.  FoundationTypes.v
  instantiates this algebra with the upstream Simplicity.Ty constructors; the
  remaining foundation work is typed Term construction and semantics.
*)

Record CoreTypeAlgebra (A : Type) := {
  core_type_unit : A;
  core_type_sum : A -> A -> A;
  core_type_prod : A -> A -> A
}.

Fixpoint translate_bridge_type
    {A : Type}
    (alg : CoreTypeAlgebra A)
    (ty : BridgeType) : option A :=
  match ty with
  | BTUnit => Some (core_type_unit alg)
  | BTSum ty_left ty_right =>
      match translate_bridge_type alg ty_left,
            translate_bridge_type alg ty_right with
      | Some translated_left, Some translated_right =>
          Some (core_type_sum alg translated_left translated_right)
      | _, _ => None
      end
  | BTProd ty_left ty_right =>
      match translate_bridge_type alg ty_left,
            translate_bridge_type alg ty_right with
      | Some translated_left, Some translated_right =>
          Some (core_type_prod alg translated_left translated_right)
      | _, _ => None
      end
  | BTAtom _ => None
  end.

Definition translate_bridge_arrow
    {A : Type}
    (alg : CoreTypeAlgebra A)
    (arrow : BridgeArrow) : option (A * A) :=
  match translate_bridge_type alg (bridge_source arrow),
        translate_bridge_type alg (bridge_target arrow) with
  | Some source, Some target => Some (source, target)
  | _, _ => None
  end.

Definition translate_option_bridge_arrow
    {A : Type}
    (alg : CoreTypeAlgebra A)
    (entry : option BridgeArrow) : option (option (A * A)) :=
  match entry with
  | Some arrow =>
      match translate_bridge_arrow alg arrow with
      | Some translated_arrow => Some (Some translated_arrow)
      | None => None
      end
  | None => Some None
  end.

Fixpoint translate_bridge_type_table
    {A : Type}
    (alg : CoreTypeAlgebra A)
    (entries : list (option BridgeArrow)) : option (list (option (A * A))) :=
  match entries with
  | [] => Some []
  | entry :: rest =>
      match translate_option_bridge_arrow alg entry,
            translate_bridge_type_table alg rest with
      | Some translated_entry, Some translated_rest =>
          Some (translated_entry :: translated_rest)
      | _, _ => None
      end
  end.

Definition translate_typed_byte_certificate_types
    {A : Type}
    (alg : CoreTypeAlgebra A)
    (certificate : CompiledMultisigTypedByteCertificate) :
    option (list (option (A * A)) * (A * A)) :=
  match translate_bridge_type_table alg (typed_certificate_types certificate),
        translate_bridge_arrow alg (typed_certificate_root_arrow certificate) with
  | Some translated_types, Some translated_root =>
      Some (translated_types, translated_root)
  | _, _ => None
  end.

Theorem translate_bridge_type_if_atom_free :
  forall A (alg : CoreTypeAlgebra A) ty,
    bridge_type_atom_free ty = true ->
    exists translated_type,
      translate_bridge_type alg ty = Some translated_type.
Proof.
  intros A alg ty.
  induction ty as [| left IHleft right IHright
                   | left IHleft right IHright
                   | tag]; intros Hatom_free; simpl in Hatom_free.
  - exists (core_type_unit alg). reflexivity.
  - apply andb_true_iff in Hatom_free as [Hleft Hright].
    destruct (IHleft Hleft) as [translated_left Htranslated_left].
    destruct (IHright Hright) as [translated_right Htranslated_right].
    simpl.
    rewrite Htranslated_left, Htranslated_right.
    eexists. reflexivity.
  - apply andb_true_iff in Hatom_free as [Hleft Hright].
    destruct (IHleft Hleft) as [translated_left Htranslated_left].
    destruct (IHright Hright) as [translated_right Htranslated_right].
    simpl.
    rewrite Htranslated_left, Htranslated_right.
    eexists. reflexivity.
  - discriminate.
Qed.

Theorem translate_bridge_arrow_if_atom_free :
  forall A (alg : CoreTypeAlgebra A) arrow,
    bridge_arrow_atom_free arrow = true ->
    exists translated_arrow,
      translate_bridge_arrow alg arrow = Some translated_arrow.
Proof.
  intros A alg [source target] Hatom_free.
  unfold bridge_arrow_atom_free in Hatom_free.
  simpl in Hatom_free.
  apply andb_true_iff in Hatom_free as [Hsource Htarget].
  destruct (@translate_bridge_type_if_atom_free A alg source Hsource)
    as [translated_source Htranslated_source].
  destruct (@translate_bridge_type_if_atom_free A alg target Htarget)
    as [translated_target Htranslated_target].
  unfold translate_bridge_arrow; simpl.
  rewrite Htranslated_source, Htranslated_target.
  eexists. reflexivity.
Qed.

Theorem translate_option_bridge_arrow_if_atom_free :
  forall A (alg : CoreTypeAlgebra A) entry,
    option_bridge_arrow_atom_free entry = true ->
    exists translated_entry,
      translate_option_bridge_arrow alg entry = Some translated_entry.
Proof.
  intros A alg [arrow |] Hatom_free.
  - simpl in Hatom_free.
    destruct (@translate_bridge_arrow_if_atom_free A alg arrow Hatom_free)
      as [translated_arrow Htranslated_arrow].
    simpl.
    rewrite Htranslated_arrow.
    eexists. reflexivity.
  - exists None. reflexivity.
Qed.

Theorem translate_bridge_type_table_if_atom_free :
  forall A (alg : CoreTypeAlgebra A) entries,
    forallb option_bridge_arrow_atom_free entries = true ->
    exists translated_entries,
      translate_bridge_type_table alg entries = Some translated_entries.
Proof.
  intros A alg entries.
  induction entries as [| entry rest IH]; intros Hatom_free.
  - exists []. reflexivity.
  - simpl in Hatom_free.
    apply andb_true_iff in Hatom_free as [Hentry Hrest].
    destruct (@translate_option_bridge_arrow_if_atom_free A alg entry Hentry)
      as [translated_entry Htranslated_entry].
    destruct (IH Hrest) as [translated_rest Htranslated_rest].
    simpl.
    rewrite Htranslated_entry, Htranslated_rest.
    eexists. reflexivity.
Qed.

Theorem translate_typed_byte_certificate_types_if_atom_free :
  forall A (alg : CoreTypeAlgebra A) certificate,
    typed_byte_certificate_atom_free certificate = true ->
    exists translated_types translated_root,
      translate_typed_byte_certificate_types alg certificate =
        Some (translated_types, translated_root).
Proof.
  intros A alg certificate Hatom_free.
  unfold typed_byte_certificate_atom_free in Hatom_free.
  apply andb_true_iff in Hatom_free as [Htypes Hroot].
  destruct
    (@translate_bridge_type_table_if_atom_free
      A alg (typed_certificate_types certificate) Htypes)
    as [translated_types Htranslated_types].
  destruct
    (@translate_bridge_arrow_if_atom_free
      A alg (typed_certificate_root_arrow certificate) Hroot)
    as [translated_root Htranslated_root].
  unfold translate_typed_byte_certificate_types.
  rewrite Htranslated_types, Htranslated_root.
  eexists. eexists. reflexivity.
Qed.
