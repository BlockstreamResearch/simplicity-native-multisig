From Coq Require Import List Arith Lia.
From MultisigFormal Require Export MultisigModel.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Section MultisigSecurity.

Variable Hash : Type.
Variable Pubkey : Type.
Variable Signature : Type.

Variable Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y}.
Variable hash_words : list Hash -> Hash.
Variable participant_message : Hash -> Hash -> Hash.
Variable vote_taproot_script_hash : Hash -> Signature -> Hash.
Variable signature_valid : Pubkey -> Signature -> Hash -> Prop.

Local Notation model_succeeds :=
  (@multisig_covenant_succeeds
    Hash Pubkey Signature Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid).
Local Notation model_base_message :=
  (@base_message Hash Hash_eq_dec hash_words).
Local Notation model_prefix_count :=
  (@multisig_prefix_count Hash Hash_eq_dec).
Local Notation model_count_votes :=
  (@CountVotes
    Hash Pubkey Signature participant_message vote_taproot_script_hash
    signature_valid).
Local Notation model_counted_vote_valid :=
  (@counted_vote_valid
    Hash Pubkey Signature participant_message vote_taproot_script_hash
    signature_valid).

Theorem multisig_success_authorizes_threshold :
  forall tx current_script_hash total_proposed_outputs
         threshold current_index participants votes,
    model_succeeds
      tx current_script_hash total_proposed_outputs
      threshold current_index participants votes ->
    exists base prefix final_input counted,
      base = model_base_message tx current_script_hash total_proposed_outputs /\
      prefix = model_prefix_count tx current_script_hash /\
      threshold <= length counted /\
      model_count_votes tx base (vote_slots participants votes)
        prefix final_input counted /\
      Forall (model_counted_vote_valid tx) counted /\
      Forall
        (fun cv => In (counted_participant cv) participants)
        counted.
Proof.
  intros tx current_script_hash total_proposed_outputs
    threshold current_index participants votes Hsuccess.
  unfold model_succeeds, multisig_covenant_succeeds in Hsuccess.
  destruct Hsuccess as
    (_Hparticipants_len &
     _Hparticipants_nodup &
     _Hvotes_len &
     _Hthreshold_min &
     _Hthreshold_max &
     _Hprefix_nonempty &
     _Hcurrent_in_prefix &
     _Hinputs_available &
     final_input & counted & Hcount & Hthreshold_counted).
  exists (model_base_message tx current_script_hash total_proposed_outputs).
  exists (model_prefix_count tx current_script_hash).
  exists final_input.
  exists counted.
  repeat split; try reflexivity; try assumption.
  - eapply CountVotes_all_counted_valid. exact Hcount.
  - pose proof (CountVotes_declared_in_entries Hcount) as Hdeclared.
    eapply Forall_impl; [| exact Hdeclared].
    intros cv Hin.
    unfold vote_slots in Hin.
    apply in_map_fst_combine_left with (votes := votes).
    exact Hin.
Qed.

Theorem multisig_success_authorizes_threshold_distinct_declared_participants :
  forall tx current_script_hash total_proposed_outputs
         threshold current_index participants votes,
    model_succeeds
      tx current_script_hash total_proposed_outputs
      threshold current_index participants votes ->
    exists base prefix final_input counted,
      base = model_base_message tx current_script_hash total_proposed_outputs /\
      prefix = model_prefix_count tx current_script_hash /\
      threshold <= length counted /\
      model_count_votes tx base (vote_slots participants votes)
        prefix final_input counted /\
      Forall (model_counted_vote_valid tx) counted /\
      Forall
        (fun cv => In (counted_participant cv) participants)
        counted /\
      NoDup (map counted_participant counted).
Proof.
  intros tx current_script_hash total_proposed_outputs
    threshold current_index participants votes Hsuccess.
  unfold model_succeeds, multisig_covenant_succeeds in Hsuccess.
  destruct Hsuccess as
    (Hparticipants_len &
     Hparticipants_nodup &
     Hvotes_len &
     Hthreshold_min &
     Hthreshold_max &
     Hprefix_nonempty &
     Hcurrent_in_prefix &
     Hinputs_available &
     final_input0 & counted0 & Hcount0 & Hthreshold_counted0).
  assert (Hsuccess :
    model_succeeds
      tx current_script_hash total_proposed_outputs
      threshold current_index participants votes).
  {
    unfold model_succeeds, multisig_covenant_succeeds.
    repeat split; try assumption.
    exists final_input0, counted0. split; assumption.
  }
  pose proof
    (multisig_success_authorizes_threshold Hsuccess)
    as (base & prefix & final_input & counted &
        Hbase & Hprefix & Hthreshold_counted &
        Hcount & Hvalid & Hdeclared).
  exists base, prefix, final_input, counted.
  repeat split; try assumption.
  eapply CountVotes_counted_participants_nodup.
  - exact Hcount.
  - unfold vote_slots.
    apply nodup_map_slot_participant_combine.
    exact Hparticipants_nodup.
Qed.

Theorem multisig_success_base_message_commits_to_prefix_and_outputs :
  forall tx current_script_hash total_proposed_outputs
         threshold current_index participants votes,
    model_succeeds
      tx current_script_hash total_proposed_outputs
      threshold current_index participants votes ->
    exists prefix,
      prefix = model_prefix_count tx current_script_hash /\
      model_base_message tx current_script_hash total_proposed_outputs =
        hash_words
          (firstn prefix (tx_input_hashes tx)
             ++ firstn total_proposed_outputs (tx_output_hashes tx)) /\
      (forall i,
        i < prefix ->
        nth_error (tx_input_script_hashes tx) i = Some current_script_hash) /\
      (nth_error (tx_input_script_hashes tx) prefix = None \/
       exists h,
         nth_error (tx_input_script_hashes tx) prefix = Some h /\
         h <> current_script_hash).
Proof.
  intros tx current_script_hash total_proposed_outputs
    threshold current_index participants votes _Hsuccess.
  exists (model_prefix_count tx current_script_hash).
  repeat split; try reflexivity.
  - intros i Hi.
    unfold multisig_prefix_count in Hi.
    unfold multisig_prefix_count.
    eapply (@prefix_count_from_before Hash Hash_eq_dec). exact Hi.
  - unfold multisig_prefix_count.
    apply (@prefix_count_from_stop Hash Hash_eq_dec).
Qed.

Theorem multisig_success_security_property :
  forall tx current_script_hash total_proposed_outputs
         threshold current_index participants votes,
    model_succeeds
      tx current_script_hash total_proposed_outputs
      threshold current_index participants votes ->
    exists base prefix final_input counted,
      base = model_base_message tx current_script_hash total_proposed_outputs /\
      prefix = model_prefix_count tx current_script_hash /\
      threshold <= length counted /\
      model_count_votes tx base (vote_slots participants votes)
        prefix final_input counted /\
      Forall (model_counted_vote_valid tx) counted /\
      Forall
        (fun cv => In (counted_participant cv) participants)
        counted /\
      NoDup (map counted_participant counted) /\
      base =
        hash_words
          (firstn prefix (tx_input_hashes tx)
             ++ firstn total_proposed_outputs (tx_output_hashes tx)) /\
      (forall i,
        i < prefix ->
        nth_error (tx_input_script_hashes tx) i = Some current_script_hash) /\
      (nth_error (tx_input_script_hashes tx) prefix = None \/
       exists h,
         nth_error (tx_input_script_hashes tx) prefix = Some h /\
         h <> current_script_hash).
Proof.
  intros tx current_script_hash total_proposed_outputs
    threshold current_index participants votes Hsuccess.
  unfold model_succeeds, multisig_covenant_succeeds in Hsuccess.
  destruct Hsuccess as
    (_Hparticipants_len &
     _Hparticipants_nodup &
     _Hvotes_len &
     _Hthreshold_min &
     _Hthreshold_max &
     _Hprefix_nonempty &
     _Hcurrent_in_prefix &
     _Hinputs_available &
     final_input & counted & Hcount & Hthreshold_counted).
  exists (model_base_message tx current_script_hash total_proposed_outputs).
  exists (model_prefix_count tx current_script_hash).
  exists final_input.
  exists counted.
  repeat split; try reflexivity; try assumption.
  - eapply CountVotes_all_counted_valid. exact Hcount.
  - pose proof (CountVotes_declared_in_entries Hcount) as Hdeclared.
    eapply Forall_impl; [| exact Hdeclared].
    intros cv Hin.
    unfold vote_slots in Hin.
    apply in_map_fst_combine_left with (votes := votes).
    exact Hin.
  - eapply CountVotes_counted_participants_nodup.
    + exact Hcount.
    + unfold vote_slots.
      apply nodup_map_slot_participant_combine.
      exact _Hparticipants_nodup.
  - intros i Hi.
    unfold multisig_prefix_count in Hi.
    unfold multisig_prefix_count.
    eapply (@prefix_count_from_before Hash Hash_eq_dec). exact Hi.
  - unfold multisig_prefix_count.
    apply (@prefix_count_from_stop Hash Hash_eq_dec).
Qed.

End MultisigSecurity.
