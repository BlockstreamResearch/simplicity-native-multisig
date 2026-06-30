From Coq Require Import List Arith Lia.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Section MultisigModel.

Variable Hash : Type.
Variable Pubkey : Type.
Variable Signature : Type.

Variable Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y}.

Variable hash_words : list Hash -> Hash.
Variable participant_message : Hash -> Hash -> Hash.
Variable vote_taproot_script_hash : Hash -> Signature -> Hash.
Variable signature_valid : Pubkey -> Signature -> Hash -> Prop.

Definition participant_count : nat := 3.

Record Tx := {
  tx_input_script_hashes : list Hash;
  tx_input_hashes : list Hash;
  tx_output_hashes : list Hash
}.

Definition tx_well_formed (tx : Tx) : Prop :=
  length (tx_input_script_hashes tx) = length (tx_input_hashes tx).

Fixpoint prefix_count_from (script : Hash) (scripts : list Hash) : nat :=
  match scripts with
  | [] => 0
  | h :: rest =>
      if Hash_eq_dec h script then S (prefix_count_from script rest) else 0
  end.

Definition multisig_prefix_count (tx : Tx) (script : Hash) : nat :=
  prefix_count_from script (tx_input_script_hashes tx).

Definition base_message
    (tx : Tx)
    (current_script_hash : Hash)
    (total_proposed_outputs : nat) : Hash :=
  hash_words
    (firstn (multisig_prefix_count tx current_script_hash) (tx_input_hashes tx)
       ++ firstn total_proposed_outputs (tx_output_hashes tx)).

Lemma prefix_count_from_before :
  forall script scripts i,
    i < prefix_count_from script scripts ->
    nth_error scripts i = Some script.
Proof.
  intros script scripts.
  induction scripts as [| h rest IH]; intros i Hlt; simpl in *.
  - lia.
  - destruct (Hash_eq_dec h script) as [Heq | Hneq].
    + subst h. destruct i as [| i].
      * reflexivity.
      * simpl. apply IH. lia.
    + lia.
Qed.

Lemma prefix_count_from_stop :
  forall script scripts,
    nth_error scripts (prefix_count_from script scripts) = None \/
    exists h,
      nth_error scripts (prefix_count_from script scripts) = Some h /\
      h <> script.
Proof.
  intros script scripts.
  induction scripts as [| h rest IH]; simpl.
  - left. reflexivity.
  - destruct (Hash_eq_dec h script) as [Heq | Hneq].
    + exact IH.
    + right. exists h. split; [reflexivity | exact Hneq].
Qed.

Record VoteEntry := {
  vote_signature : Signature;
  vote_executable_leaf_hash : Hash
}.

Record CountedVote := {
  counted_participant : Pubkey;
  counted_signature : Signature;
  counted_leaf_hash : Hash;
  counted_input_index : nat;
  counted_base_message : Hash
}.

Definition counted_vote_authorizes (cv : CountedVote) : Prop :=
  signature_valid
    (counted_participant cv)
    (counted_signature cv)
    (participant_message (counted_leaf_hash cv) (counted_base_message cv)).

Definition counted_vote_input_commits (tx : Tx) (cv : CountedVote) : Prop :=
  nth_error (tx_input_script_hashes tx) (counted_input_index cv) =
    Some (vote_taproot_script_hash (counted_leaf_hash cv) (counted_signature cv)).

Definition counted_vote_valid (tx : Tx) (cv : CountedVote) : Prop :=
  counted_vote_authorizes cv /\ counted_vote_input_commits tx cv.

Definition vote_slots
    (participants : list Pubkey)
    (votes : list (option VoteEntry)) : list (Pubkey * option VoteEntry) :=
  combine participants votes.

Definition slot_participant (slot : Pubkey * option VoteEntry) : Pubkey :=
  fst slot.

Inductive CountVotes (tx : Tx) (base : Hash) :
    list (Pubkey * option VoteEntry) ->
    nat -> nat -> list CountedVote -> Prop :=
| CountVotes_nil :
    forall next_input,
      CountVotes tx base [] next_input next_input []
| CountVotes_none :
    forall participant rest next_input final_input counted,
      CountVotes tx base rest next_input final_input counted ->
      CountVotes tx base
        ((participant, None) :: rest)
        next_input final_input counted
| CountVotes_some :
    forall participant vote rest next_input final_input counted,
      signature_valid participant
        (vote_signature vote)
        (participant_message (vote_executable_leaf_hash vote) base) ->
      nth_error (tx_input_script_hashes tx) next_input =
        Some (vote_taproot_script_hash
          (vote_executable_leaf_hash vote)
          (vote_signature vote)) ->
      CountVotes tx base rest (S next_input) final_input counted ->
      CountVotes tx base
        ((participant, Some vote) :: rest)
        next_input final_input
        ({|
          counted_participant := participant;
          counted_signature := vote_signature vote;
          counted_leaf_hash := vote_executable_leaf_hash vote;
          counted_input_index := next_input;
          counted_base_message := base
        |} :: counted).

Lemma CountVotes_all_counted_valid :
  forall tx base entries next_input final_input counted,
    CountVotes tx base entries next_input final_input counted ->
    Forall (counted_vote_valid tx) counted.
Proof.
  intros tx base entries next_input final_input counted Hcount.
  induction Hcount.
  - constructor.
  - exact IHHcount.
  - constructor.
    + split; simpl; assumption.
    + exact IHHcount.
Qed.

Lemma CountVotes_declared_in_entries :
  forall tx base entries next_input final_input counted,
    CountVotes tx base entries next_input final_input counted ->
    Forall
      (fun cv => In (counted_participant cv) (map slot_participant entries))
      counted.
Proof.
  intros tx base entries next_input final_input counted Hcount.
  induction Hcount.
  - constructor.
  - simpl. eapply Forall_impl; [| exact IHHcount].
    intros cv Hin. right. exact Hin.
  - simpl. constructor.
    + left. reflexivity.
    + eapply Forall_impl; [| exact IHHcount].
      intros cv Hin. right. exact Hin.
Qed.

Lemma CountVotes_counted_participants_nodup :
  forall tx base entries next_input final_input counted,
    CountVotes tx base entries next_input final_input counted ->
    NoDup (map slot_participant entries) ->
    NoDup (map counted_participant counted).
Proof.
  intros tx base entries next_input final_input counted Hcount.
  induction Hcount; intros Hnodup; simpl in *.
  - constructor.
  - inversion Hnodup as [| head tail Hnotin Hnodup_tail]; subst.
    apply IHHcount. exact Hnodup_tail.
  - inversion Hnodup as [| head tail Hnotin Hnodup_tail]; subst.
    constructor.
    + intro Hin.
      apply Hnotin.
      pose proof (CountVotes_declared_in_entries Hcount) as Hdeclared.
      rewrite Forall_forall in Hdeclared.
      rewrite in_map_iff in Hin.
      destruct Hin as (cv & Hparticipant & Hcv_in).
      rewrite <- Hparticipant.
      apply Hdeclared. exact Hcv_in.
    + apply IHHcount. exact Hnodup_tail.
Qed.

Lemma in_map_fst_combine_left :
  forall (x : Pubkey) participants votes,
    In x (map slot_participant (combine participants votes)) ->
    In x participants.
Proof.
  intros x participants.
  induction participants as [| participant participants IH];
    intros votes Hin; destruct votes as [| vote votes]; simpl in *.
  - contradiction.
  - contradiction.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + left. exact Heq.
    + right. apply IH with (votes := votes). exact Hin.
Qed.

Lemma nodup_map_slot_participant_combine :
  forall participants votes,
    NoDup participants ->
    NoDup (map slot_participant (combine participants votes)).
Proof.
  intros participants.
  induction participants as [| participant participants IH];
    intros votes Hnodup; destruct votes as [| vote votes]; simpl.
  - constructor.
  - constructor.
  - constructor.
  - inversion Hnodup; subst.
    constructor.
    + intro Hin.
      apply H1.
      apply in_map_fst_combine_left with (votes := votes).
      exact Hin.
    + apply IH. assumption.
Qed.

Definition multisig_covenant_succeeds
    (tx : Tx)
    (current_script_hash : Hash)
    (total_proposed_outputs threshold current_index : nat)
    (participants : list Pubkey)
    (votes : list (option VoteEntry)) : Prop :=
  let prefix := multisig_prefix_count tx current_script_hash in
  let base := base_message tx current_script_hash total_proposed_outputs in
  length participants = participant_count /\
  NoDup participants /\
  length votes = participant_count /\
  1 <= threshold /\
  threshold <= participant_count /\
  1 <= prefix /\
  current_index < prefix /\
  threshold + prefix <= length (tx_input_script_hashes tx) /\
  exists final_input counted,
    CountVotes tx base (vote_slots participants votes) prefix final_input counted /\
    threshold <= length counted.

End MultisigModel.

Arguments tx_input_script_hashes {Hash} _.
Arguments tx_input_hashes {Hash} _.
Arguments tx_output_hashes {Hash} _.
Arguments prefix_count_from {Hash Hash_eq_dec} script scripts.
Arguments multisig_prefix_count {Hash Hash_eq_dec} tx script.
Arguments base_message {Hash Hash_eq_dec hash_words}
  tx current_script_hash total_proposed_outputs.
Arguments vote_signature {Hash Signature} _.
Arguments vote_executable_leaf_hash {Hash Signature} _.
Arguments counted_participant {Hash Pubkey Signature} _.
Arguments counted_signature {Hash Pubkey Signature} _.
Arguments counted_leaf_hash {Hash Pubkey Signature} _.
Arguments counted_input_index {Hash Pubkey Signature} _.
Arguments counted_base_message {Hash Pubkey Signature} _.
Arguments counted_vote_authorizes
  {Hash Pubkey Signature participant_message signature_valid} cv.
Arguments counted_vote_input_commits
  {Hash Pubkey Signature vote_taproot_script_hash} tx cv.
Arguments counted_vote_valid
  {Hash Pubkey Signature participant_message vote_taproot_script_hash
   signature_valid} tx cv.
Arguments vote_slots {Hash Pubkey Signature} participants votes.
Arguments CountVotes
  {Hash Pubkey Signature participant_message vote_taproot_script_hash
   signature_valid} tx base entries next_input final_input counted.
Arguments multisig_covenant_succeeds
  {Hash Pubkey Signature Hash_eq_dec hash_words participant_message
   vote_taproot_script_hash signature_valid}
  tx current_script_hash total_proposed_outputs threshold current_index
  participants votes.
