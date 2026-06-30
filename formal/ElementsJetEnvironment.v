From Coq Require Import Bool Arith List PeanoNat.
From MultisigFormal Require Import
  ElementsJets ElementsJetSemantics MultisigSecurity MultisigSourceBlocks.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Section ElementsJetEnvironment.

Variables Hash Pubkey Signature Ctx8 Word256 : Type.

Variable sem : ElementsJetSemantics Hash Pubkey Signature Ctx8 Word256.
Variable Hsem : ElementsJetSemanticsSpec sem.

Local Notation sem_static_parameter_asserts_succeed :=
  (@static_parameter_asserts_succeed Hash Pubkey Signature Ctx8 Word256 sem).
Local Notation sem_prefix_asserts_succeed :=
  (@prefix_asserts_succeed Hash Pubkey Signature Ctx8 Word256 sem).
Local Notation sem_minimum_inputs_asserts_succeed :=
  (@minimum_inputs_asserts_succeed Hash Pubkey Signature Ctx8 Word256 sem).
Local Notation sem_static_parameter_asserts_imply_source_checks :=
  (@static_parameter_asserts_imply_source_checks
    Hash Pubkey Signature Ctx8 Word256 sem Hsem).
Local Notation sem_prefix_asserts_imply_source_prefix_checks :=
  (@prefix_asserts_imply_source_prefix_checks
    Hash Pubkey Signature Ctx8 Word256 sem Hsem).
Local Notation sem_minimum_inputs_asserts_imply_inputs_available :=
  (@minimum_inputs_asserts_imply_inputs_available
    Hash Pubkey Signature Ctx8 Word256 sem Hsem).

Record ElementsEnvTxRelation
    (env : ElementsEnv Word256)
    (tx : Tx Hash)
    (current_script_hash : Hash) : Prop := {
  env_tx_current_script_hash :
    sem_word256_as_hash sem (env_current_script_hash env) =
      current_script_hash;
  env_tx_num_inputs :
    env_num_inputs env = length (tx_input_script_hashes tx);
  env_tx_num_input_hashes :
    env_num_inputs env = length (tx_input_hashes tx);
  env_tx_input_script_hash :
    forall index,
      option_map (sem_word256_as_hash sem)
        (env_input_script_hash env index) =
      nth_error (tx_input_script_hashes tx) index;
  env_tx_input_hash :
    forall index,
      option_map (sem_word256_as_hash sem)
        (env_input_hash env index) =
      nth_error (tx_input_hashes tx) index;
  env_tx_output_hash :
    forall index,
      option_map (sem_word256_as_hash sem)
        (env_output_hash env index) =
      nth_error (tx_output_hashes tx) index
}.

Theorem elements_env_tx_relation_well_formed :
  forall env tx current_script_hash,
    ElementsEnvTxRelation env tx current_script_hash ->
    tx_well_formed tx.
Proof.
  intros env tx current_script_hash Henv.
  destruct Henv as [_ Hscripts Hinput_hashes _ _ _].
  unfold tx_well_formed.
  rewrite <- Hscripts.
  rewrite <- Hinput_hashes.
  reflexivity.
Qed.

Theorem elements_env_current_script_hash_matches_model :
  forall env tx current_script_hash,
    ElementsEnvTxRelation env tx current_script_hash ->
    sem_word256_as_hash sem (sem_current_script_hash sem env) =
      current_script_hash.
Proof.
  intros env tx current_script_hash Henv.
  destruct Henv as [Hcurrent _ _ _ _ _].
  rewrite (spec_current_script_hash Hsem env).
  exact Hcurrent.
Qed.

Theorem elements_env_input_script_hash_matches_model :
  forall env tx current_script_hash index,
    ElementsEnvTxRelation env tx current_script_hash ->
    option_map (sem_word256_as_hash sem)
      (sem_input_script_hash sem env index) =
    nth_error (tx_input_script_hashes tx) index.
Proof.
  intros env tx current_script_hash index Henv.
  destruct Henv as [_ _ _ Hscripts _ _].
  rewrite (spec_input_script_hash Hsem env index).
  exact (Hscripts index).
Qed.

Theorem elements_env_input_hash_matches_model :
  forall env tx current_script_hash index,
    ElementsEnvTxRelation env tx current_script_hash ->
    option_map (sem_word256_as_hash sem)
      (sem_input_hash sem env index) =
    nth_error (tx_input_hashes tx) index.
Proof.
  intros env tx current_script_hash index Henv.
  destruct Henv as [_ _ _ _ Hinput_hashes _].
  rewrite (spec_input_hash Hsem env index).
  exact (Hinput_hashes index).
Qed.

Theorem elements_env_output_hash_matches_model :
  forall env tx current_script_hash index,
    ElementsEnvTxRelation env tx current_script_hash ->
    option_map (sem_word256_as_hash sem)
      (sem_output_hash sem env index) =
    nth_error (tx_output_hashes tx) index.
Proof.
  intros env tx current_script_hash index Henv.
  destruct Henv as [_ _ _ _ _ Houtput_hashes].
  rewrite (spec_output_hash Hsem env index).
  exact (Houtput_hashes index).
Qed.

Theorem minimum_inputs_asserts_imply_model_inputs_available :
  forall env tx current_script_hash threshold prefix carry minimum_inputs_num,
    ElementsEnvTxRelation env tx current_script_hash ->
    sem_minimum_inputs_asserts_succeed
      threshold
      prefix
      (sem_num_inputs sem env)
      carry
      minimum_inputs_num ->
    threshold + prefix <= length (tx_input_script_hashes tx).
Proof.
  intros env tx current_script_hash threshold prefix carry
    minimum_inputs_num Henv Hminimum.
  assert (Havailable : threshold + prefix <= sem_num_inputs sem env).
  {
    eapply sem_minimum_inputs_asserts_imply_inputs_available.
    exact Hminimum.
  }
  rewrite (spec_num_inputs Hsem env) in Havailable.
  destruct Henv as [_ Hnum_inputs _ _ _ _].
  rewrite Hnum_inputs in Havailable.
  exact Havailable.
Qed.

Definition static_prefix_minimum_asserts_succeed
    (threshold : U32)
    (participant1 participant2 participant3 : U256 Word256)
    (env : ElementsEnv Word256)
    (prefix : U32)
    (carry : bool)
    (minimum_inputs_num : U32) : Prop :=
  sem_static_parameter_asserts_succeed
    threshold participant1 participant2 participant3 /\
  sem_prefix_asserts_succeed env prefix /\
  sem_minimum_inputs_asserts_succeed
    threshold
    prefix
    (sem_num_inputs sem env)
    carry
    minimum_inputs_num.

Theorem static_prefix_minimum_asserts_imply_source_block_premises :
  forall (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         env tx current_script_hash threshold current_index
         participant1 participant2 participant3 prefix carry
         minimum_inputs_num,
    ElementsEnvTxRelation env tx current_script_hash ->
    current_index = env_current_index env ->
    prefix =
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash ->
    static_prefix_minimum_asserts_succeed
      threshold
      participant1
      participant2
      participant3
      env
      prefix
      carry
      minimum_inputs_num ->
    static_parameter_checks_succeed
      (sem_eq_256 sem)
      threshold
      participant1
      participant2
      participant3 /\
    1 <= @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash /\
    current_index <
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash /\
    threshold + @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash <=
      length (tx_input_script_hashes tx).
Proof.
  intros Hash_eq_dec env tx current_script_hash threshold current_index
    participant1 participant2 participant3 prefix carry minimum_inputs_num
    Henv Hcurrent_index Hprefix Hasserts.
  unfold static_prefix_minimum_asserts_succeed in Hasserts.
  destruct Hasserts as [Hstatic [Hprefix_asserts Hminimum]].
  pose proof
    (sem_static_parameter_asserts_imply_source_checks Hstatic)
    as Hsource_static.
  pose proof
    (sem_prefix_asserts_imply_source_prefix_checks Hprefix_asserts)
    as [Hprefix_nonempty Hcurrent_lt].
  pose proof
    (minimum_inputs_asserts_imply_model_inputs_available Henv Hminimum)
    as Hinputs_available.
  subst current_index.
  rewrite Hprefix in Hprefix_nonempty.
  rewrite Hprefix in Hcurrent_lt.
  rewrite Hprefix in Hinputs_available.
  split.
  - exact Hsource_static.
  - split.
    + exact Hprefix_nonempty.
    + split.
      * exact Hcurrent_lt.
	      * exact Hinputs_available.
Qed.

Theorem static_prefix_minimum_and_votes_imply_source_blocks :
  forall (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : U256 Word256 -> Signature -> Hash -> Prop)
         env tx current_script_hash total_proposed_outputs
         threshold current_index participant1 participant2 participant3
         votes final_input counted prefix carry minimum_inputs_num,
    ElementsEnvTxRelation env tx current_script_hash ->
    current_index = env_current_index env ->
    prefix =
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash ->
    static_prefix_minimum_asserts_succeed
      threshold
      participant1
      participant2
      participant3
      env
      prefix
      carry
      minimum_inputs_num ->
    length votes = participant_count ->
    @CountVotes
      Hash
      (U256 Word256)
      Signature
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      (@base_message
        Hash
        Hash_eq_dec
        hash_words
        tx
        current_script_hash
        total_proposed_outputs)
      (@vote_slots
        Hash
        (U256 Word256)
        Signature
        [participant1; participant2; participant3]
        votes)
      prefix
      final_input
      counted ->
    threshold <= length counted ->
    @multisig_source_blocks_succeed
      (U256 Word256)
      (sem_eq_256 sem)
      Hash
      Signature
      Hash_eq_dec
      hash_words
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      current_script_hash
      total_proposed_outputs
      threshold
      current_index
      participant1
      participant2
      participant3
      votes
      final_input
      counted.
Proof.
  intros Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid env tx current_script_hash
    total_proposed_outputs threshold current_index participant1 participant2
    participant3 votes final_input counted prefix carry minimum_inputs_num
    Henv Hcurrent_index Hprefix Hasserts Hvotes_len Hcount
    Hthreshold_counted.
  pose proof
    (@static_prefix_minimum_asserts_imply_source_block_premises
      Hash_eq_dec
      env
      tx
      current_script_hash
      threshold
      current_index
      participant1
      participant2
      participant3
      prefix
      carry
      minimum_inputs_num
      Henv
      Hcurrent_index
      Hprefix
      Hasserts)
    as (Hstatic & Hprefix_nonempty & Hcurrent_lt & Hinputs_available).
  unfold multisig_source_blocks_succeed.
  split.
  - exact Hstatic.
  - split.
    + exact Hvotes_len.
    + split.
      * exact Hprefix_nonempty.
      * split.
        -- exact Hcurrent_lt.
        -- split.
           ++ exact Hinputs_available.
           ++ split.
              ** rewrite <- Hprefix.
                 exact Hcount.
              ** exact Hthreshold_counted.
Qed.

Theorem static_prefix_minimum_and_votes_imply_model_success :
  forall (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : U256 Word256 -> Signature -> Hash -> Prop)
         env tx current_script_hash total_proposed_outputs
         threshold current_index participant1 participant2 participant3
         votes final_input counted prefix carry minimum_inputs_num,
    ElementsEnvTxRelation env tx current_script_hash ->
    current_index = env_current_index env ->
    prefix =
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash ->
    static_prefix_minimum_asserts_succeed
      threshold
      participant1
      participant2
      participant3
      env
      prefix
      carry
      minimum_inputs_num ->
    length votes = participant_count ->
    @CountVotes
      Hash
      (U256 Word256)
      Signature
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      (@base_message
        Hash
        Hash_eq_dec
        hash_words
        tx
        current_script_hash
        total_proposed_outputs)
      (@vote_slots
        Hash
        (U256 Word256)
        Signature
        [participant1; participant2; participant3]
        votes)
      prefix
      final_input
      counted ->
    threshold <= length counted ->
    @multisig_covenant_succeeds
      Hash
      (U256 Word256)
      Signature
      Hash_eq_dec
      hash_words
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      current_script_hash
      total_proposed_outputs
      threshold
      current_index
      [participant1; participant2; participant3]
      votes.
Proof.
  intros Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid env tx current_script_hash
    total_proposed_outputs threshold current_index participant1 participant2
    participant3 votes final_input counted prefix carry minimum_inputs_num
    Henv Hcurrent_index Hprefix Hasserts Hvotes_len Hcount
    Hthreshold_counted.
  eapply (@multisig_source_blocks_imply_model_success
    (U256 Word256)
    (sem_eq_256 sem)).
  - intros x y Heq.
    eapply (@elements_sem_eq_256_false_neq
      Hash Pubkey Signature Ctx8 Word256 sem Hsem).
    exact Heq.
  - eapply static_prefix_minimum_and_votes_imply_source_blocks.
    + exact Henv.
    + exact Hcurrent_index.
    + exact Hprefix.
    + exact Hasserts.
    + exact Hvotes_len.
    + exact Hcount.
    + exact Hthreshold_counted.
Qed.

End ElementsJetEnvironment.
