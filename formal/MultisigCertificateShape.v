From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Import
  MultisigCertificateCore MultisigSecurity MultisigSourceBlocks
  SimplicityByteDecoder.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma threshold_well_formed_sound :
  forall threshold,
    threshold_well_formed threshold = true ->
    1 <= threshold /\ threshold <= participant_count.
Proof.
  intros threshold Hthreshold.
  unfold threshold_well_formed in Hthreshold.
  apply andb_true_iff in Hthreshold as [Hmin Hmax].
  apply Nat.leb_le in Hmin.
  apply Nat.leb_le in Hmax.
  unfold participant_count.
  split; assumption.
Qed.

Lemma participant_bytes_well_formed_sound :
  forall participant,
    participant_bytes_well_formed participant = true ->
    length participant = 32 /\ bytes_well_formed participant = true.
Proof.
  intros participant Hparticipant.
  unfold participant_bytes_well_formed in Hparticipant.
  apply andb_true_iff in Hparticipant as [Hlength Hbytes].
  apply Nat.eqb_eq in Hlength.
  split; assumption.
Qed.

Lemma bytes_eqb_refl :
  forall bytes,
    bytes_eqb bytes bytes = true.
Proof.
  induction bytes as [| byte rest IH].
  - reflexivity.
  - simpl.
    rewrite Nat.eqb_refl.
    exact IH.
Qed.

Lemma bytes_eqb_true_eq :
  forall lhs rhs,
    bytes_eqb lhs rhs = true ->
    lhs = rhs.
Proof.
  induction lhs as [| left rest_left IH];
    intros rhs Heq;
    destruct rhs as [| right rest_right];
    simpl in Heq; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Heq as [Hhead Htail].
    apply Nat.eqb_eq in Hhead.
    apply IH in Htail.
    subst.
    reflexivity.
Qed.

Lemma bytes_eqb_false_neq :
  forall lhs rhs,
    bytes_eqb lhs rhs = false ->
    lhs <> rhs.
Proof.
  intros lhs rhs Heq Hsame.
  subst rhs.
  rewrite bytes_eqb_refl in Heq.
  discriminate Heq.
Qed.

Lemma bytes_neq_bytes_eqb_false :
  forall lhs rhs,
    lhs <> rhs ->
    bytes_eqb lhs rhs = false.
Proof.
  intros lhs rhs Hneq.
  destruct (bytes_eqb lhs rhs) eqn:Heq.
  - apply bytes_eqb_true_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Lemma participants_distinct_well_formed_sound :
  forall participants,
    participants_distinct_well_formed participants = true ->
    NoDup participants.
Proof.
  intros participants Hdistinct.
  destruct participants as
    [| participant1 [| participant2 [| participant3 [| extra rest]]]];
    simpl in Hdistinct; try discriminate.
  repeat rewrite andb_true_iff in Hdistinct.
  destruct Hdistinct as [[H12 H13] H23].
  apply negb_true_iff in H12.
  apply negb_true_iff in H13.
  apply negb_true_iff in H23.
  pose proof (bytes_eqb_false_neq H12) as H12neq.
  pose proof (bytes_eqb_false_neq H13) as H13neq.
  pose proof (bytes_eqb_false_neq H23) as H23neq.
  repeat constructor.
  - intros Hin.
    destruct Hin as [Heq | [Heq | []]]; subst.
    + apply H12neq. reflexivity.
    + apply H13neq. reflexivity.
  - intros Hin.
    destruct Hin as [Heq | []]; subst.
    apply H23neq. reflexivity.
  - intros Hin. contradiction.
Qed.

Lemma participants_well_formed_sound :
  forall participants,
    participants_well_formed participants = true ->
    length participants = participant_count /\
    NoDup participants /\
    Forall
      (fun participant =>
        length participant = 32 /\ bytes_well_formed participant = true)
      participants.
Proof.
  intros participants Hparticipants.
  unfold participants_well_formed in Hparticipants.
  repeat rewrite andb_true_iff in Hparticipants.
  destruct Hparticipants as [[Hlength Hall] Hdistinct].
  apply Nat.eqb_eq in Hlength.
  rewrite forallb_forall in Hall.
  repeat split.
  - unfold participant_count. exact Hlength.
  - apply participants_distinct_well_formed_sound.
    exact Hdistinct.
  - rewrite Forall_forall.
    intros participant Hin.
    apply participant_bytes_well_formed_sound.
    apply Hall. exact Hin.
Qed.

Theorem certificate_shape_well_formed_sound :
  forall certificate,
    certificate_shape_well_formed certificate = true ->
    certificate_static_fields_well_formed certificate.
Proof.
  intros certificate Hshape.
  unfold certificate_shape_well_formed in Hshape.
  repeat rewrite andb_true_iff in Hshape.
  destruct Hshape as
    ((((Hthreshold & Hparticipants) & Hprogram) & Hcmr_length) & Hcmr_bytes).
  pose proof
    (threshold_well_formed_sound (cert_threshold certificate) Hthreshold)
    as [Hthreshold_min Hthreshold_max].
  pose proof
    (participants_well_formed_sound
      (cert_participants certificate)
      Hparticipants)
    as [Hparticipants_length [Hparticipants_nodup Hparticipants_fields]].
  apply Nat.eqb_eq in Hcmr_length.
  unfold certificate_static_fields_well_formed.
  repeat split; assumption.
Qed.

Theorem certificate_static_fields_imply_source_static_parameter_checks :
  forall certificate participant1 participant2 participant3,
    cert_participants certificate =
      [participant1; participant2; participant3] ->
    certificate_static_fields_well_formed certificate ->
    @static_parameter_checks_succeed
      (list byte)
      bytes_eqb
      (cert_threshold certificate)
      participant1
      participant2
      participant3.
Proof.
  intros certificate participant1 participant2 participant3
    Hparticipants Hstatic.
  destruct Hstatic as
    (Hthreshold_min &
     Hthreshold_max &
     _Hparticipants_length &
     Hparticipants_nodup &
     _Hparticipants_fields &
     _Hprogram_bytes &
     _Hcmr_length &
     _Hcmr_bytes).
  unfold static_parameter_checks_succeed.
  split.
  - unfold threshold_checks_succeed.
    split.
    + exact Hthreshold_min.
    + exact Hthreshold_max.
  - unfold ensure_distinct_participants_succeeds.
    rewrite Hparticipants in Hparticipants_nodup.
    inversion Hparticipants_nodup as [| head tail Hnotin_head Hnodup_tail];
      subst.
    inversion Hnodup_tail as [| head_tail tail_tail Hnotin_tail _];
      subst.
    repeat split.
    + apply bytes_neq_bytes_eqb_false.
      intros Heq.
      subst participant2.
      apply Hnotin_head.
      left. reflexivity.
    + apply bytes_neq_bytes_eqb_false.
      intros Heq.
      subst participant3.
      apply Hnotin_head.
      right. left. reflexivity.
    + apply bytes_neq_bytes_eqb_false.
      intros Heq.
      subst participant3.
      apply Hnotin_tail.
      left. reflexivity.
Qed.
