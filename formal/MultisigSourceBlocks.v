From Coq Require Import List Arith Lia.
From MultisigFormal Require Import MultisigSecurity.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Source-level lemmas for individual SIMF blocks in
  crates/contracts/simf/multisig_n_of_3.simf.

  These lemmas are the source-semantics side of the bridge into
  multisig_covenant_succeeds. They are intentionally small and named after the
  source blocks they justify.
*)

Section SourceBlocks.

Variable Pubkey : Type.
Variable pubkey_eqb : Pubkey -> Pubkey -> bool.

Variable pubkey_eqb_false_neq :
  forall x y,
    pubkey_eqb x y = false ->
    x <> y.

Definition ensure_distinct_participants_succeeds
    (participant1 participant2 participant3 : Pubkey) : Prop :=
  pubkey_eqb participant1 participant2 = false /\
  pubkey_eqb participant1 participant3 = false /\
  pubkey_eqb participant2 participant3 = false.

Theorem ensure_distinct_participants_implies_NoDup :
  forall participant1 participant2 participant3,
    ensure_distinct_participants_succeeds
      participant1 participant2 participant3 ->
    NoDup [participant1; participant2; participant3].
Proof.
  intros participant1 participant2 participant3 Hdistinct.
  unfold ensure_distinct_participants_succeeds in Hdistinct.
  destruct Hdistinct as (H12 & H13 & H23).
  pose proof (pubkey_eqb_false_neq H12) as H12neq.
  pose proof (pubkey_eqb_false_neq H13) as H13neq.
  pose proof (pubkey_eqb_false_neq H23) as H23neq.
  repeat constructor.
  - intros Hin. destruct Hin as [Heq | [Heq | []]]; subst.
    + apply H12neq. reflexivity.
    + apply H13neq. reflexivity.
  - intros Hin. destruct Hin as [Heq | []]; subst.
    apply H23neq. reflexivity.
  - intros Hin. contradiction.
Qed.

Definition threshold_checks_succeed (threshold : nat) : Prop :=
  1 <= threshold /\ threshold <= 3.

Theorem threshold_checks_imply_model_bounds :
  forall threshold,
    threshold_checks_succeed threshold ->
    1 <= threshold /\ threshold <= participant_count.
Proof.
  intros threshold Hthreshold.
  unfold threshold_checks_succeed in Hthreshold.
  unfold participant_count.
  exact Hthreshold.
Qed.

Definition static_parameter_checks_succeed
    (threshold : nat)
    (participant1 participant2 participant3 : Pubkey) : Prop :=
  threshold_checks_succeed threshold /\
  ensure_distinct_participants_succeeds
    participant1 participant2 participant3.

Theorem static_parameter_checks_imply_model_static_fields :
  forall threshold participant1 participant2 participant3,
    static_parameter_checks_succeed
      threshold participant1 participant2 participant3 ->
    length [participant1; participant2; participant3] = participant_count /\
    NoDup [participant1; participant2; participant3] /\
    1 <= threshold /\
    threshold <= participant_count.
Proof.
  intros threshold participant1 participant2 participant3 Hstatic.
  unfold static_parameter_checks_succeed in Hstatic.
  destruct Hstatic as [Hthreshold Hdistinct].
  pose proof
    (@threshold_checks_imply_model_bounds threshold Hthreshold)
    as [Hthreshold_min Hthreshold_max].
  pose proof
    (@ensure_distinct_participants_implies_NoDup
      participant1 participant2 participant3 Hdistinct)
    as Hnodup.
  split.
  - unfold participant_count. reflexivity.
  - split.
    + exact Hnodup.
    + split.
      * exact Hthreshold_min.
      * exact Hthreshold_max.
Qed.

Variable Hash : Type.
Variable Signature : Type.

Variable Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y}.
Variable hash_words : list Hash -> Hash.
Variable participant_message : Hash -> Hash -> Hash.
Variable vote_taproot_script_hash : Hash -> Signature -> Hash.
Variable signature_valid : Pubkey -> Signature -> Hash -> Prop.

Definition multisig_source_blocks_succeed
    (tx : Tx Hash)
    (current_script_hash : Hash)
    (total_proposed_outputs threshold current_index : nat)
    (participant1 participant2 participant3 : Pubkey)
    (votes : list (option (VoteEntry Hash Signature)))
    (final_input : nat)
    (counted : list (CountedVote Hash Pubkey Signature)) : Prop :=
  let participants := [participant1; participant2; participant3] in
  let prefix :=
    @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash in
  let base :=
    @base_message
      Hash
      Hash_eq_dec
      hash_words
      tx
      current_script_hash
      total_proposed_outputs in
  static_parameter_checks_succeed
    threshold participant1 participant2 participant3 /\
  length votes = participant_count /\
  1 <= prefix /\
  current_index < prefix /\
  threshold + prefix <= length (tx_input_script_hashes tx) /\
  @CountVotes
    Hash
    Pubkey
    Signature
    participant_message
    vote_taproot_script_hash
    signature_valid
    tx
    base
    (@vote_slots Hash Pubkey Signature participants votes)
    prefix
    final_input
    counted /\
  threshold <= length counted.

Theorem multisig_source_blocks_imply_model_success :
  forall tx current_script_hash total_proposed_outputs
         threshold current_index
         participant1 participant2 participant3 votes
         final_input counted,
    multisig_source_blocks_succeed
      tx
      current_script_hash
      total_proposed_outputs
      threshold
      current_index
      participant1 participant2 participant3
      votes
      final_input
      counted ->
    @multisig_covenant_succeeds
      Hash
      Pubkey
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
  intros tx current_script_hash total_proposed_outputs
    threshold current_index participant1 participant2 participant3
    votes final_input counted Hsource.
  unfold multisig_source_blocks_succeed in Hsource.
  destruct Hsource as
    (Hstatic &
     Hvotes_len &
     Hprefix_nonempty &
     Hcurrent_in_prefix &
     Hinputs_available &
     Hcount &
     Hthreshold_counted).
  pose proof
    (@static_parameter_checks_imply_model_static_fields
      threshold participant1 participant2 participant3 Hstatic)
    as
      (Hparticipants_len &
       Hparticipants_nodup &
       Hthreshold_min &
       Hthreshold_max).
  unfold multisig_covenant_succeeds.
  repeat split; try assumption.
  exists final_input, counted.
  split; assumption.
Qed.

End SourceBlocks.
