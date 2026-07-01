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

Definition vote_input_script_hash_assert_succeeds
    (vote_taproot_script_hash : Hash -> Signature -> Hash)
    (env : ElementsEnv Word256)
    (next_input : U32)
    (vote : VoteEntry Hash Signature) : Prop :=
  exists script_hash_word,
    sem_input_script_hash sem env next_input = Some script_hash_word /\
    sem_word256_as_hash sem script_hash_word =
      vote_taproot_script_hash
        (vote_executable_leaf_hash vote)
        (vote_signature vote).

Definition vote_threshold_assert_succeeds
    (threshold counted_count : U32) : Prop :=
  assert_true_succeeds sem (sem_le_32 sem threshold counted_count).

Inductive ElementsVoteSlotsExecution
    (participant_message : Hash -> Hash -> Hash)
    (vote_taproot_script_hash : Hash -> Signature -> Hash)
    (signature_valid : U256 Word256 -> Signature -> Hash -> Prop)
    (env : ElementsEnv Word256)
    (base : Hash) :
    list (U256 Word256 * option (VoteEntry Hash Signature)) ->
    U32 -> U32 -> U32 ->
    list (CountedVote Hash (U256 Word256) Signature) -> Prop :=
| ElementsVoteSlotsExecution_nil :
    forall next_input,
      ElementsVoteSlotsExecution
        participant_message
        vote_taproot_script_hash
        signature_valid
        env
        base
        []
        next_input
        next_input
        0
        []
| ElementsVoteSlotsExecution_none :
    forall participant rest next_input final_input counted_count counted,
      ElementsVoteSlotsExecution
        participant_message
        vote_taproot_script_hash
        signature_valid
        env
        base
        rest
        next_input
        final_input
        counted_count
        counted ->
      ElementsVoteSlotsExecution
        participant_message
        vote_taproot_script_hash
        signature_valid
        env
        base
        ((participant, None) :: rest)
        next_input
        final_input
        counted_count
        counted
| ElementsVoteSlotsExecution_some :
    forall participant vote rest next_input final_input
           counted_count counted,
      signature_valid
        participant
        (vote_signature vote)
        (participant_message (vote_executable_leaf_hash vote) base) ->
      vote_input_script_hash_assert_succeeds
        vote_taproot_script_hash
        env
        next_input
        vote ->
      ElementsVoteSlotsExecution
        participant_message
        vote_taproot_script_hash
        signature_valid
        env
        base
        rest
        (S next_input)
        final_input
        counted_count
        counted ->
      ElementsVoteSlotsExecution
        participant_message
        vote_taproot_script_hash
        signature_valid
        env
        base
        ((participant, Some vote) :: rest)
        next_input
        final_input
        (S counted_count)
        ({|
          counted_participant := participant;
          counted_signature := vote_signature vote;
          counted_leaf_hash := vote_executable_leaf_hash vote;
          counted_input_index := next_input;
          counted_base_message := base
        |} :: counted).

Theorem elements_vote_slots_execution_implies_count_votes :
  forall (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : U256 Word256 -> Signature -> Hash -> Prop)
         env tx current_script_hash base entries
         next_input final_input counted_count counted,
    ElementsEnvTxRelation env tx current_script_hash ->
    ElementsVoteSlotsExecution
      participant_message
      vote_taproot_script_hash
      signature_valid
      env
      base
      entries
      next_input
      final_input
      counted_count
      counted ->
    @CountVotes
      Hash
      (U256 Word256)
      Signature
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      base
      entries
      next_input
      final_input
      counted /\
    counted_count = length counted.
Proof.
  intros participant_message vote_taproot_script_hash signature_valid
    env tx current_script_hash base entries next_input final_input
    counted_count counted Henv Hexec.
  induction Hexec.
  - split.
    + constructor.
    + reflexivity.
  - destruct IHHexec as [Hcount Hcounted_count].
    split.
    + constructor. exact Hcount.
    + exact Hcounted_count.
  - destruct IHHexec as [Hcount Hcounted_count].
    unfold vote_input_script_hash_assert_succeeds in H0.
    destruct H0 as [script_hash_word [Hscript Hscript_hash]].
    pose proof
      (@elements_env_input_script_hash_matches_model
        env
        tx
        current_script_hash
        next_input
        Henv) as Hinput_script_hash.
    rewrite Hscript in Hinput_script_hash.
    simpl in Hinput_script_hash.
    rewrite Hscript_hash in Hinput_script_hash.
    split.
    + econstructor.
      * exact H.
      * symmetry. exact Hinput_script_hash.
      * exact Hcount.
    + simpl. rewrite <- Hcounted_count. reflexivity.
Qed.

Theorem vote_threshold_assert_implies_threshold_counted :
  forall threshold counted_count
         (counted : list (CountedVote Hash (U256 Word256) Signature)),
    counted_count = length counted ->
    vote_threshold_assert_succeeds threshold counted_count ->
    threshold <= length counted.
Proof.
  intros threshold counted_count counted Hcount Hthreshold.
  unfold vote_threshold_assert_succeeds in Hthreshold.
  unfold assert_true_succeeds in Hthreshold.
  apply (proj1 (spec_verify Hsem (sem_le_32 sem threshold counted_count)))
    in Hthreshold.
  rewrite <- Hcount.
  eapply (@elements_sem_le_32_true_le
    Hash Pubkey Signature Ctx8 Word256 sem Hsem).
  exact Hthreshold.
Qed.

Theorem elements_vote_execution_and_threshold_assert_imply_count_votes :
  forall (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : U256 Word256 -> Signature -> Hash -> Prop)
         env tx current_script_hash base entries
         next_input final_input counted_count counted threshold,
    ElementsEnvTxRelation env tx current_script_hash ->
    ElementsVoteSlotsExecution
      participant_message
      vote_taproot_script_hash
      signature_valid
      env
      base
      entries
      next_input
      final_input
      counted_count
      counted ->
    vote_threshold_assert_succeeds threshold counted_count ->
    @CountVotes
      Hash
      (U256 Word256)
      Signature
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      base
      entries
      next_input
      final_input
      counted /\
    threshold <= length counted.
Proof.
  intros participant_message vote_taproot_script_hash signature_valid
    env tx current_script_hash base entries next_input final_input
    counted_count counted threshold Henv Hexec Hthreshold.
  pose proof
    (@elements_vote_slots_execution_implies_count_votes
      participant_message
      vote_taproot_script_hash
      signature_valid
      env
      tx
      current_script_hash
      base
      entries
      next_input
      final_input
      counted_count
      counted
      Henv
      Hexec) as [Hcount Hcounted_count].
  split.
  - exact Hcount.
  - eapply vote_threshold_assert_implies_threshold_counted.
    + exact Hcounted_count.
    + exact Hthreshold.
Qed.

Theorem static_prefix_minimum_and_executed_votes_imply_model_success :
  forall (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : U256 Word256 -> Signature -> Hash -> Prop)
         env tx current_script_hash total_proposed_outputs
         threshold current_index participant1 participant2 participant3
         votes final_input counted_count counted prefix carry
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
    length votes = participant_count ->
    ElementsVoteSlotsExecution
      participant_message
      vote_taproot_script_hash
      signature_valid
      env
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
      counted_count
      counted ->
    vote_threshold_assert_succeeds threshold counted_count ->
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
    participant3 votes final_input counted_count counted prefix carry
    minimum_inputs_num Henv Hcurrent_index Hprefix Hasserts Hvotes_len
    Hexec Hthreshold.
  pose proof
    (@elements_vote_execution_and_threshold_assert_imply_count_votes
      participant_message
      vote_taproot_script_hash
      signature_valid
      env
      tx
      current_script_hash
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
      counted_count
      counted
      threshold
      Henv
      Hexec
      Hthreshold) as [Hcount Hthreshold_counted].
  eapply static_prefix_minimum_and_votes_imply_model_success.
  - exact Henv.
  - exact Hcurrent_index.
  - exact Hprefix.
  - exact Hasserts.
  - exact Hvotes_len.
  - exact Hcount.
  - exact Hthreshold_counted.
Qed.

End ElementsJetEnvironment.
