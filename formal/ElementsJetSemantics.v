From Coq Require Import Bool Arith List PeanoNat.
From MultisigFormal Require Import
  ElementsJets MultisigSecurity MultisigSourceBlocks.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Contract-specific semantic laws for the whitelisted Elements jets.

  ElementsJets.v fixes the syntactic jet subset and byte decoder scope.  This
  module starts the semantic side of the bridge: a later foundation/Elements
  evaluator must supply an ElementsJetSemantics value plus this specification.
  The theorems below then turn successful low-level assertions into the source
  block premises used by MultisigSourceBlocks.v.
*)

Definition u8_modulus : nat := Nat.pow 2 8.
Definition u16_modulus : nat := Nat.pow 2 16.

Section ElementsJetSemanticSpec.

Variables Hash Pubkey Signature Ctx8 Word256 : Type.

Variable sem : ElementsJetSemantics Hash Pubkey Signature Ctx8 Word256.

Record ElementsJetSemanticsSpec : Type := {
  spec_add_32_no_carry :
    forall x y result,
      sem_add_32 sem x y = (false, result) ->
      result = x + y;
  spec_increment_32_no_carry :
    forall x result,
      sem_increment_32 sem x = (false, result) ->
      result = S x;
  spec_eq_1 :
    forall x y,
      sem_eq_1 sem x y = Bool.eqb x y;
  spec_eq_16 :
    forall x y,
      sem_eq_16 sem x y = Nat.eqb x y;
  spec_eq_32 :
    forall x y,
      sem_eq_32 sem x y = Nat.eqb x y;
  spec_eq_256 :
    forall x y : U256 Word256,
      sem_eq_256 sem x y = true <-> x = y;
  spec_le_32 :
    forall x y,
      sem_le_32 sem x y = Nat.leb x y;
  spec_lt_32 :
    forall x y,
      sem_lt_32 sem x y = Nat.ltb x y;
  spec_left_pad_low_8_32 :
    forall x,
      x < u8_modulus ->
      sem_left_pad_low_8_32 sem x = x;
  spec_left_pad_low_16_32 :
    forall x,
      x < u16_modulus ->
      sem_left_pad_low_16_32 sem x = x;
  spec_current_index :
    forall env,
      sem_current_index sem env = env_current_index env;
  spec_num_inputs :
    forall env,
      sem_num_inputs sem env = env_num_inputs env;
  spec_current_script_hash :
    forall env,
      sem_current_script_hash sem env = env_current_script_hash env;
  spec_input_script_hash :
    forall env index,
      sem_input_script_hash sem env index = env_input_script_hash env index;
  spec_input_hash :
    forall env index,
      sem_input_hash sem env index = env_input_hash env index;
  spec_output_hash :
    forall env index,
      sem_output_hash sem env index = env_output_hash env index;
  spec_verify :
    forall bit,
      sem_verify sem bit <-> bit = true
}.

Variable Hsem : ElementsJetSemanticsSpec.

Definition assert_true_succeeds (bit : bool) : Prop :=
  sem_verify sem bit.

Definition ensure_zero_bit_succeeds (bit : bool) : Prop :=
  sem_verify sem (negb bit).

Theorem assert_true_succeeds_true :
  forall bit,
    assert_true_succeeds bit ->
    bit = true.
Proof.
  intros bit Hassert.
  unfold assert_true_succeeds in Hassert.
  apply (proj1 (spec_verify Hsem bit)).
  exact Hassert.
Qed.

Theorem ensure_zero_bit_succeeds_false :
  forall bit,
    ensure_zero_bit_succeeds bit ->
    bit = false.
Proof.
  intros bit Hzero.
  unfold ensure_zero_bit_succeeds in Hzero.
  apply (proj1 (spec_verify Hsem (negb bit))) in Hzero.
  apply Bool.negb_true_iff in Hzero.
  exact Hzero.
Qed.

Theorem elements_sem_eq_256_true :
  forall x y : U256 Word256,
    sem_eq_256 sem x y = true ->
    x = y.
Proof.
  intros x y Heq.
  apply (proj1 (spec_eq_256 Hsem x y)).
  exact Heq.
Qed.

Theorem elements_sem_eq_256_false_neq :
  forall x y : U256 Word256,
    sem_eq_256 sem x y = false ->
    x <> y.
Proof.
  intros x y Heq Hxy.
  pose proof (proj2 (spec_eq_256 Hsem x y) Hxy) as Heq_true.
  rewrite Heq in Heq_true.
  discriminate.
Qed.

Theorem elements_sem_le_32_true_le :
  forall x y,
    sem_le_32 sem x y = true ->
    x <= y.
Proof.
  intros x y Hle.
  rewrite (spec_le_32 Hsem x y) in Hle.
  apply Nat.leb_le.
  exact Hle.
Qed.

Theorem elements_sem_lt_32_true_lt :
  forall x y,
    sem_lt_32 sem x y = true ->
    x < y.
Proof.
  intros x y Hlt.
  rewrite (spec_lt_32 Hsem x y) in Hlt.
  apply Nat.ltb_lt.
  exact Hlt.
Qed.

Theorem elements_sem_add_32_no_carry_exact :
  forall x y result,
    sem_add_32 sem x y = (false, result) ->
    result = x + y.
Proof.
  intros x y result Hadd.
  eapply (spec_add_32_no_carry Hsem).
  exact Hadd.
Qed.

Theorem elements_sem_increment_32_no_carry_exact :
  forall x result,
    sem_increment_32 sem x = (false, result) ->
    result = S x.
Proof.
  intros x result Hincrement.
  eapply (spec_increment_32_no_carry Hsem).
  exact Hincrement.
Qed.

Definition threshold_asserts_succeed (threshold : U32) : Prop :=
  assert_true_succeeds (sem_le_32 sem 1 threshold) /\
  assert_true_succeeds (sem_le_32 sem threshold 3).

Theorem threshold_asserts_imply_source_checks :
  forall threshold,
    threshold_asserts_succeed threshold ->
    threshold_checks_succeed threshold.
Proof.
  intros threshold Hthreshold.
  unfold threshold_asserts_succeed in Hthreshold.
  destruct Hthreshold as [Hmin Hmax].
  unfold assert_true_succeeds in Hmin, Hmax.
  apply (proj1 (spec_verify Hsem (sem_le_32 sem 1 threshold))) in Hmin.
  apply (proj1 (spec_verify Hsem (sem_le_32 sem threshold 3))) in Hmax.
  split.
  - eapply elements_sem_le_32_true_le.
    exact Hmin.
  - eapply elements_sem_le_32_true_le.
    exact Hmax.
Qed.

Definition ensure_distinct_participant_words_succeed
    (participant1 participant2 participant3 : U256 Word256) : Prop :=
  ensure_zero_bit_succeeds (sem_eq_256 sem participant1 participant2) /\
  ensure_zero_bit_succeeds (sem_eq_256 sem participant1 participant3) /\
  ensure_zero_bit_succeeds (sem_eq_256 sem participant2 participant3).

Theorem ensure_distinct_participant_words_imply_source_checks :
  forall participant1 participant2 participant3 : U256 Word256,
    ensure_distinct_participant_words_succeed
      participant1 participant2 participant3 ->
    ensure_distinct_participants_succeeds
      (sem_eq_256 sem)
      participant1
      participant2
      participant3.
Proof.
  intros participant1 participant2 participant3 Hdistinct.
  unfold ensure_distinct_participant_words_succeed in Hdistinct.
  destruct Hdistinct as [H12 [H13 H23]].
  repeat split;
    apply ensure_zero_bit_succeeds_false;
    assumption.
Qed.

Theorem ensure_distinct_participant_words_imply_NoDup :
  forall participant1 participant2 participant3 : U256 Word256,
    ensure_distinct_participant_words_succeed
      participant1 participant2 participant3 ->
    NoDup [participant1; participant2; participant3].
Proof.
  intros participant1 participant2 participant3 Hdistinct.
  eapply (@ensure_distinct_participants_implies_NoDup
    (U256 Word256)
    (sem_eq_256 sem)).
  - intros x y Heq.
    eapply elements_sem_eq_256_false_neq.
    exact Heq.
  - eapply ensure_distinct_participant_words_imply_source_checks.
    exact Hdistinct.
Qed.

Definition static_parameter_asserts_succeed
    (threshold : U32)
    (participant1 participant2 participant3 : U256 Word256) : Prop :=
  threshold_asserts_succeed threshold /\
  ensure_distinct_participant_words_succeed
    participant1 participant2 participant3.

Theorem static_parameter_asserts_imply_source_checks :
  forall threshold participant1 participant2 participant3,
    static_parameter_asserts_succeed
      threshold participant1 participant2 participant3 ->
    static_parameter_checks_succeed
      (sem_eq_256 sem)
      threshold
      participant1
      participant2
      participant3.
Proof.
  intros threshold participant1 participant2 participant3 Hstatic.
  unfold static_parameter_asserts_succeed in Hstatic.
  destruct Hstatic as [Hthreshold Hdistinct].
  split.
  - eapply threshold_asserts_imply_source_checks.
    exact Hthreshold.
  - eapply ensure_distinct_participant_words_imply_source_checks.
    exact Hdistinct.
Qed.

Theorem static_parameter_asserts_imply_model_static_fields :
  forall threshold participant1 participant2 participant3,
    static_parameter_asserts_succeed
      threshold participant1 participant2 participant3 ->
    length [participant1; participant2; participant3] = participant_count /\
    NoDup [participant1; participant2; participant3] /\
    1 <= threshold /\
    threshold <= participant_count.
Proof.
  intros threshold participant1 participant2 participant3 Hstatic.
  eapply (@static_parameter_checks_imply_model_static_fields
    (U256 Word256)
    (sem_eq_256 sem)).
  - intros x y Heq.
    eapply elements_sem_eq_256_false_neq.
    exact Heq.
  - eapply static_parameter_asserts_imply_source_checks.
    exact Hstatic.
Qed.

Definition minimum_inputs_asserts_succeed
    (threshold prefix num_inputs : U32)
    (carry : bool)
    (minimum_inputs_num : U32) : Prop :=
  sem_add_32 sem threshold prefix = (carry, minimum_inputs_num) /\
  ensure_zero_bit_succeeds carry /\
  assert_true_succeeds (sem_le_32 sem minimum_inputs_num num_inputs).

Theorem minimum_inputs_asserts_imply_inputs_available :
  forall threshold prefix num_inputs carry minimum_inputs_num,
    minimum_inputs_asserts_succeed
      threshold prefix num_inputs carry minimum_inputs_num ->
    threshold + prefix <= num_inputs.
Proof.
  intros threshold prefix num_inputs carry minimum_inputs_num Hminimum.
  unfold minimum_inputs_asserts_succeed in Hminimum.
  destruct Hminimum as [Hadd [Hcarry Hle]].
  unfold ensure_zero_bit_succeeds in Hcarry.
  apply (proj1 (spec_verify Hsem (negb carry))) in Hcarry.
  apply Bool.negb_true_iff in Hcarry.
  unfold assert_true_succeeds in Hle.
  apply
    (proj1 (spec_verify Hsem (sem_le_32 sem minimum_inputs_num num_inputs)))
    in Hle.
  subst carry.
  assert (Hminimum_inputs_num : minimum_inputs_num = threshold + prefix).
  {
    eapply (spec_add_32_no_carry Hsem).
    exact Hadd.
  }
  rewrite Hminimum_inputs_num in Hle.
  eapply elements_sem_le_32_true_le.
  exact Hle.
Qed.

Definition prefix_nonempty_assert_succeeds (prefix : U32) : Prop :=
  assert_true_succeeds (sem_le_32 sem 1 prefix).

Definition current_index_assert_succeeds
    (env : ElementsEnv Word256)
    (prefix : U32) : Prop :=
  assert_true_succeeds (sem_lt_32 sem (sem_current_index sem env) prefix).

Definition prefix_asserts_succeed
    (env : ElementsEnv Word256)
    (prefix : U32) : Prop :=
  prefix_nonempty_assert_succeeds prefix /\
  current_index_assert_succeeds env prefix.

Theorem prefix_nonempty_assert_implies_source_prefix_nonempty :
  forall prefix,
    prefix_nonempty_assert_succeeds prefix ->
    1 <= prefix.
Proof.
  intros prefix Hprefix.
  unfold prefix_nonempty_assert_succeeds, assert_true_succeeds in Hprefix.
  apply (proj1 (spec_verify Hsem (sem_le_32 sem 1 prefix))) in Hprefix.
  eapply elements_sem_le_32_true_le.
  exact Hprefix.
Qed.

Theorem current_index_assert_implies_source_current_index :
  forall env prefix,
    current_index_assert_succeeds env prefix ->
    env_current_index env < prefix.
Proof.
  intros env prefix Hcurrent.
  unfold current_index_assert_succeeds, assert_true_succeeds in Hcurrent.
  apply
    (proj1
      (spec_verify Hsem (sem_lt_32 sem (sem_current_index sem env) prefix)))
    in Hcurrent.
  rewrite (spec_current_index Hsem env) in Hcurrent.
  eapply elements_sem_lt_32_true_lt.
  exact Hcurrent.
Qed.

Theorem prefix_asserts_imply_source_prefix_checks :
  forall env prefix,
    prefix_asserts_succeed env prefix ->
    1 <= prefix /\
    env_current_index env < prefix.
Proof.
  intros env prefix Hprefix.
  unfold prefix_asserts_succeed in Hprefix.
  destruct Hprefix as [Hnonempty Hcurrent].
  split.
  - eapply prefix_nonempty_assert_implies_source_prefix_nonempty.
    exact Hnonempty.
  - eapply current_index_assert_implies_source_current_index.
    exact Hcurrent.
Qed.

End ElementsJetSemanticSpec.
