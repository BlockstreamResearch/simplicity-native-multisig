Require Import Simplicity.Ty.
From MultisigFormal Require Import
  BridgeTypeTranslation MultisigTypedCertificate TypedBridge.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Narrow adapter to the upstream Simplicity foundation type language.

  This intentionally imports only Simplicity.Ty.  The heavier foundation modules
  for CMRs, primitive semantics, and bit-machine evaluation still depend on the
  SHA/VST stack.  Ty.v is standalone, so the formal audit can already check that
  the decoded atom-free bridge type certificate translates to the actual
  foundation Unit/Sum/Prod constructors.
*)

Definition simplicity_ty_core_type_algebra : CoreTypeAlgebra Ty := {|
  core_type_unit := Unit;
  core_type_sum := Sum;
  core_type_prod := Prod
|}.

Definition translate_bridge_type_to_simplicity_ty :
    BridgeType -> option Ty :=
  translate_bridge_type simplicity_ty_core_type_algebra.

Definition translate_bridge_arrow_to_simplicity_ty :
    BridgeArrow -> option (Ty * Ty) :=
  translate_bridge_arrow simplicity_ty_core_type_algebra.

Definition translate_bridge_type_table_to_simplicity_ty :
    list (option BridgeArrow) -> option (list (option (Ty * Ty))) :=
  translate_bridge_type_table simplicity_ty_core_type_algebra.

Definition translate_typed_byte_certificate_types_to_simplicity_ty
    (certificate : CompiledMultisigTypedByteCertificate) :
    option (list (option (Ty * Ty)) * (Ty * Ty)) :=
  translate_typed_byte_certificate_types
    simplicity_ty_core_type_algebra
    certificate.

Theorem translate_bridge_type_to_simplicity_ty_if_atom_free :
  forall ty,
    bridge_type_atom_free ty = true ->
    exists translated_type,
      translate_bridge_type_to_simplicity_ty ty = Some translated_type.
Proof.
  intros ty Hatom_free.
  unfold translate_bridge_type_to_simplicity_ty.
  eapply translate_bridge_type_if_atom_free.
  exact Hatom_free.
Qed.

Theorem translate_bridge_arrow_to_simplicity_ty_if_atom_free :
  forall arrow,
    bridge_arrow_atom_free arrow = true ->
    exists translated_arrow,
      translate_bridge_arrow_to_simplicity_ty arrow = Some translated_arrow.
Proof.
  intros arrow Hatom_free.
  unfold translate_bridge_arrow_to_simplicity_ty.
  eapply translate_bridge_arrow_if_atom_free.
  exact Hatom_free.
Qed.

Theorem translate_typed_byte_certificate_types_to_simplicity_ty_if_atom_free :
  forall certificate,
    typed_byte_certificate_atom_free certificate = true ->
    exists translated_types translated_root,
      translate_typed_byte_certificate_types_to_simplicity_ty certificate =
        Some (translated_types, translated_root).
Proof.
  intros certificate Hatom_free.
  unfold translate_typed_byte_certificate_types_to_simplicity_ty.
  eapply translate_typed_byte_certificate_types_if_atom_free.
  exact Hatom_free.
Qed.
