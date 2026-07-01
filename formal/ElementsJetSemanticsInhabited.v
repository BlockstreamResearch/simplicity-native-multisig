(*
  ElementsJetSemanticsInhabited.v — G1/G2 increment: the whitelisted-jet
  semantic interface `ElementsJetSemanticsSpec` is INHABITED.

  The audit review noted that every semantic-bridge theorem is quantified over an
  abstract `sem : ElementsJetSemantics` and `Hsem : ElementsJetSemanticsSpec sem`
  that were never instantiated, so it was not evident the premise is satisfiable.
  This file constructs a concrete evaluator and proves it satisfies the spec, so
  those theorems are conditional on a SATISFIABLE (non-vacuous) premise.

  Scope note: the spec constrains only the arithmetic / comparison / environment
  jets; the SHA-256 context, tapbranch/taptweak and BIP-0340 fields carry no spec
  laws, so this witness leaves them trivial.  This proves consistency of the
  interface; it does NOT claim the deployed compiled program's jets satisfy it —
  that still requires the Simplicity semantic foundation (eval / Primitive), which
  is not vendored here.
*)

From Coq Require Import Bool Arith List PeanoNat Lia.
From MultisigFormal Require Import ElementsJets ElementsJetSemantics.
Import ListNotations.

Definition u32_modulus : nat := Nat.pow 2 32.
(* Keep opaque: 2^32 as a unary nat is intractable for cbn/simpl. *)
Opaque u32_modulus.

(* A concrete evaluator over nat-typed words/hashes/keys. *)
Definition concrete_elements_jet_semantics
  : ElementsJetSemantics nat nat nat nat nat :=
  {| sem_add_32 := fun x y => if Nat.ltb (x + y) u32_modulus
                              then (false, x + y)
                              else (true, (x + y) mod u32_modulus)
   ; sem_increment_32 := fun x => if Nat.ltb (S x) u32_modulus
                                  then (false, S x)
                                  else (true, (S x) mod u32_modulus)
   ; sem_eq_1 := Bool.eqb
   ; sem_eq_16 := Nat.eqb
   ; sem_eq_32 := Nat.eqb
   ; sem_eq_256 := Nat.eqb
   ; sem_le_32 := Nat.leb
   ; sem_lt_32 := Nat.ltb
   ; sem_left_pad_low_8_32 := fun x => x
   ; sem_left_pad_low_16_32 := fun x => x
   ; sem_current_index := fun e => env_current_index e
   ; sem_num_inputs := fun e => env_num_inputs e
   ; sem_current_script_hash := fun e => env_current_script_hash e
   ; sem_input_script_hash := fun e i => env_input_script_hash e i
   ; sem_input_hash := fun e i => env_input_hash e i
   ; sem_output_hash := fun e i => env_output_hash e i
   ; sem_sha_256_ctx_8_init := 0
   ; sem_tapdata_init := 0
   ; sem_sha_256_ctx_8_add_2 := fun c _ => c
   ; sem_sha_256_ctx_8_add_32 := fun c _ => c
   ; sem_sha_256_ctx_8_add_64 := fun c _ => c
   ; sem_sha_256_ctx_8_finalize := fun _ => 0
   ; sem_build_tapbranch := fun _ _ => 0
   ; sem_build_taptweak := fun _ _ => 0
   ; sem_bip_0340_verify := fun _ _ _ => True
   ; sem_verify := fun bit => bit = true
   ; sem_word256_as_hash := fun w => w
   ; sem_word256_as_pubkey := fun w => w
  |}.

Theorem concrete_elements_jet_semantics_spec :
  ElementsJetSemanticsSpec concrete_elements_jet_semantics.
Proof.
  constructor.
  - (* add_32 no carry *)
    intros x y result H;
    cbv [sem_add_32 concrete_elements_jet_semantics] in H;
    destruct (Nat.ltb (x + y) u32_modulus); congruence.
  - (* increment_32 no carry *)
    intros x result H;
    cbv [sem_increment_32 concrete_elements_jet_semantics] in H;
    destruct (Nat.ltb (S x) u32_modulus); congruence.
  - (* eq_1 *)  intros; reflexivity.
  - (* eq_16 *) intros; reflexivity.
  - (* eq_32 *) intros; reflexivity.
  - (* eq_256 *) intros x y; cbn; apply Nat.eqb_eq.
  - (* le_32 *) intros; reflexivity.
  - (* lt_32 *) intros; reflexivity.
  - (* left_pad_8 *)  intros; reflexivity.
  - (* left_pad_16 *) intros; reflexivity.
  - (* current_index *)      intros; reflexivity.
  - (* num_inputs *)         intros; reflexivity.
  - (* current_script_hash *) intros; reflexivity.
  - (* input_script_hash *)  intros; reflexivity.
  - (* input_hash *)         intros; reflexivity.
  - (* output_hash *)        intros; reflexivity.
  - (* verify *) intros bit; cbn; tauto.
Qed.

(* The semantic interface is inhabited: a concrete evaluator together with a proof
   it meets the spec.  (ElementsJetSemanticsSpec is Type-valued, so we package the
   witness as a sigT rather than a Prop-level exists.)  This makes explicit that
   the bridge theorems' `Hsem : ElementsJetSemanticsSpec sem` premise is
   satisfiable, not vacuous. *)
Definition elements_jet_semantics_spec_inhabited :
  { sem : ElementsJetSemantics nat nat nat nat nat & ElementsJetSemanticsSpec sem } :=
  existT _ concrete_elements_jet_semantics concrete_elements_jet_semantics_spec.
