Require Import Simplicity.Ty.
From MultisigFormal Require Import CompiledMultisigTypedExample FoundationTypes.

Set Implicit Arguments.
Set Strict Implicit.

Theorem compiled_multisig_typed_certificate_translates_to_simplicity_ty :
  exists typed_certificate translated_types translated_root,
    compiled_multisig_typed_certificate = Some typed_certificate /\
    translate_typed_byte_certificate_types_to_simplicity_ty typed_certificate =
      Some (translated_types, translated_root).
Proof.
  pose proof
    (@compiled_multisig_typed_certificate_translates_to_core_type_algebra
      Ty
      simplicity_ty_core_type_algebra)
    as [typed_certificate [translated_types [translated_root
         [Hcertificate Htranslated]]]].
  exists typed_certificate, translated_types, translated_root.
  split.
  - exact Hcertificate.
  - exact Htranslated.
Qed.
