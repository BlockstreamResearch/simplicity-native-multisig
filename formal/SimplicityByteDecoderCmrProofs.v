From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderCmrCore.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Lemma compute_cmr_nodes_length :
  forall alg nodes computed computed',
    compute_cmr_nodes alg nodes computed = Some computed' ->
    length computed' = length computed + length nodes.
Proof.
  intros alg nodes.
  induction nodes as [| node rest IH];
    intros computed computed' Hcompute; simpl in Hcompute.
  - inversion Hcompute; subst. rewrite Nat.add_0_r. reflexivity.
  - destruct (compute_converted_node_cmr alg computed node) as [node_cmr |]
      eqn:Hnode; [| discriminate].
    specialize (IH (computed ++ [node_cmr]) computed' Hcompute).
    rewrite IH.
    rewrite length_app.
    simpl.
    rewrite <- Nat.add_assoc.
    reflexivity.
Qed.

Lemma compute_cmr_nodes_checked_length :
  forall alg nodes computed computed',
    compute_cmr_nodes_checked alg nodes computed = Some computed' ->
    length computed' = length computed + length nodes.
Proof.
  intros alg nodes.
  induction nodes as [| node rest IH];
    intros computed computed' Hcompute; simpl in Hcompute.
  - inversion Hcompute; subst. rewrite Nat.add_0_r. reflexivity.
  - destruct (compute_converted_node_cmr alg computed node) as [node_cmr |]
      eqn:Hnode; [| discriminate].
    destruct (require_cmr_bits node_cmr) as [checked_cmr |] eqn:Hcheck;
      [| discriminate].
    specialize (IH (computed ++ [checked_cmr]) computed' Hcompute).
    rewrite IH.
    rewrite length_app.
    simpl.
    rewrite <- Nat.add_assoc.
    reflexivity.
Qed.

Lemma cmr_bits_well_formed_true_length :
  forall cmr_bits,
    cmr_bits_well_formed cmr_bits = true ->
    length cmr_bits = 256.
Proof.
  intros cmr_bits Hwell_formed.
  unfold cmr_bits_well_formed in Hwell_formed.
  apply Nat.eqb_eq. exact Hwell_formed.
Qed.

Lemma bits_eqb_true_eq :
  forall lhs rhs,
    bits_eqb lhs rhs = true ->
    lhs = rhs.
Proof.
  induction lhs as [| lhs_bit lhs_rest IH];
    intros rhs Hbits; destruct rhs as [| rhs_bit rhs_rest];
    simpl in Hbits; try discriminate.
  - reflexivity.
  - apply andb_true_iff in Hbits as [Hhead Htail].
    destruct lhs_bit, rhs_bit; simpl in Hhead; try discriminate;
      f_equal; apply IH; exact Htail.
Qed.

Theorem verify_structural_program_cmr_sound :
  forall alg program expected_cmr,
    verify_structural_program_cmr alg program expected_cmr = true ->
    compute_structural_program_cmr alg program = Some expected_cmr.
Proof.
  intros alg program expected_cmr Hverify.
  unfold verify_structural_program_cmr in Hverify.
  destruct (compute_structural_program_cmr alg program) as [actual_cmr |]
    eqn:Hcompute; [| discriminate].
  apply bits_eqb_true_eq in Hverify.
  rewrite <- Hverify.
  reflexivity.
Qed.

Theorem verify_structural_program_cmr_checked_sound :
  forall alg program expected_cmr,
    verify_structural_program_cmr_checked alg program expected_cmr = true ->
    compute_structural_program_cmr_checked alg program = Some expected_cmr /\
    length expected_cmr = 256.
Proof.
  intros alg program expected_cmr Hverify.
  unfold verify_structural_program_cmr_checked in Hverify.
  unfold require_cmr_bits in Hverify.
  destruct (cmr_bits_well_formed expected_cmr) eqn:Hexpected;
    [| discriminate].
  destruct (compute_structural_program_cmr_checked alg program)
    as [actual_cmr |] eqn:Hcompute; [| discriminate].
  apply bits_eqb_true_eq in Hverify.
  subst actual_cmr.
  split.
  - reflexivity.
  - apply cmr_bits_well_formed_true_length. exact Hexpected.
Qed.

Theorem decode_structural_program_bytes_with_cmr_sound :
  forall alg bytes expected_cmr program,
    decode_structural_program_bytes_with_cmr alg bytes expected_cmr =
      Some program ->
    decode_structural_program_bytes bytes = Some program /\
    compute_structural_program_cmr alg program = Some expected_cmr.
Proof.
  intros alg bytes expected_cmr program Hdecode.
  unfold decode_structural_program_bytes_with_cmr in Hdecode.
  destruct (decode_structural_program_bytes bytes) as [decoded_program |]
    eqn:Hprogram; [| discriminate].
  destruct (verify_structural_program_cmr alg decoded_program expected_cmr)
    eqn:Hverify; [| discriminate].
  inversion Hdecode; subst decoded_program.
  split.
  - reflexivity.
  - apply verify_structural_program_cmr_sound. exact Hverify.
Qed.

Theorem decode_structural_program_bytes_streaming_with_cmr_sound :
  forall alg bytes expected_cmr program,
    decode_structural_program_bytes_streaming_with_cmr alg bytes expected_cmr =
      Some program ->
    decode_structural_program_bytes_streaming bytes = Some program /\
    compute_structural_program_cmr alg program = Some expected_cmr.
Proof.
  intros alg bytes expected_cmr program Hdecode.
  unfold decode_structural_program_bytes_streaming_with_cmr in Hdecode.
  destruct (decode_structural_program_bytes_streaming bytes)
    as [decoded_program |] eqn:Hprogram; [| discriminate].
  destruct (verify_structural_program_cmr alg decoded_program expected_cmr)
    eqn:Hverify; [| discriminate].
  inversion Hdecode; subst decoded_program.
  split.
  - reflexivity.
  - apply verify_structural_program_cmr_sound. exact Hverify.
Qed.

Theorem decode_structural_program_bytes_with_checked_cmr_sound :
  forall alg bytes expected_cmr program,
    decode_structural_program_bytes_with_checked_cmr alg bytes expected_cmr =
      Some program ->
    decode_structural_program_bytes bytes = Some program /\
    compute_structural_program_cmr_checked alg program = Some expected_cmr /\
    length expected_cmr = 256.
Proof.
  intros alg bytes expected_cmr program Hdecode.
  unfold decode_structural_program_bytes_with_checked_cmr in Hdecode.
  destruct (decode_structural_program_bytes bytes) as [decoded_program |]
    eqn:Hprogram; [| discriminate].
  destruct (verify_structural_program_cmr_checked alg decoded_program expected_cmr)
    eqn:Hverify; [| discriminate].
  inversion Hdecode; subst decoded_program.
  split.
  - reflexivity.
  - apply verify_structural_program_cmr_checked_sound. exact Hverify.
Qed.

Theorem decode_structural_program_bytes_streaming_with_checked_cmr_sound :
  forall alg bytes expected_cmr program,
    decode_structural_program_bytes_streaming_with_checked_cmr
      alg bytes expected_cmr =
      Some program ->
    decode_structural_program_bytes_streaming bytes = Some program /\
    compute_structural_program_cmr_checked alg program =
      Some expected_cmr /\
    length expected_cmr = 256.
Proof.
  intros alg bytes expected_cmr program Hdecode.
  unfold decode_structural_program_bytes_streaming_with_checked_cmr in Hdecode.
  destruct (decode_structural_program_bytes_streaming bytes)
    as [decoded_program |] eqn:Hprogram; [| discriminate].
  destruct (verify_structural_program_cmr_checked alg decoded_program expected_cmr)
    eqn:Hverify; [| discriminate].
  inversion Hdecode; subst decoded_program.
  split.
  - reflexivity.
  - apply verify_structural_program_cmr_checked_sound. exact Hverify.
Qed.

Definition toy_unary_cmr (tag child : CmrBits) : CmrBits :=
  tag ++ child.

Definition toy_binary_cmr (tag lhs rhs : CmrBits) : CmrBits :=
  tag ++ lhs ++ rhs.

Definition toy_cmr_alg : CmrAlgebra := {|
  cmr_iden := [false; false; false];
  cmr_unit := [false; false; true];
  cmr_injl := toy_unary_cmr [false; true; false];
  cmr_injr := toy_unary_cmr [false; true; true];
  cmr_take := toy_unary_cmr [true; false; false];
  cmr_drop := toy_unary_cmr [true; false; true];
  cmr_comp := toy_binary_cmr [true; true; false; false];
  cmr_case := toy_binary_cmr [true; true; false; true];
  cmr_pair := toy_binary_cmr [true; true; true; false];
  cmr_disconnect := toy_unary_cmr [true; true; true; true];
  cmr_witness := [false; true; false; false];
  cmr_fail := toy_unary_cmr [false; true; false; true];
  cmr_jet := fun jet => [true] ++ bits_of_elements_jet jet;
  cmr_word := fun encoded_width value_bits =>
    [false] ++ bits_of_nat 6 encoded_width ++ value_bits
|}.

Definition zero_cmr_alg : CmrAlgebra := {|
  cmr_iden := zero_hash256_bits;
  cmr_unit := zero_hash256_bits;
  cmr_injl := fun _ => zero_hash256_bits;
  cmr_injr := fun _ => zero_hash256_bits;
  cmr_take := fun _ => zero_hash256_bits;
  cmr_drop := fun _ => zero_hash256_bits;
  cmr_comp := fun _ _ => zero_hash256_bits;
  cmr_case := fun _ _ => zero_hash256_bits;
  cmr_pair := fun _ _ => zero_hash256_bits;
  cmr_disconnect := fun _ => zero_hash256_bits;
  cmr_witness := zero_hash256_bits;
  cmr_fail := fun _ => zero_hash256_bits;
  cmr_jet := fun _ => zero_hash256_bits;
  cmr_word := fun _ _ => zero_hash256_bits
|}.

Example decode_natural_one :
  decode_natural [false] = Some (1, []).
Proof. reflexivity. Qed.

Example decode_natural_two :
  decode_natural [true; false; false] = Some (2, []).
Proof. reflexivity. Qed.

Example decode_raw_node_unit :
  decode_raw_node 0 [false; true; false; false; true] =
    Some (RUnit, []).
Proof. reflexivity. Qed.

Example decode_raw_node_rejects_fail_code :
  decode_raw_node 0 [false; true; false; true; false] = None.
Proof. reflexivity. Qed.

Example decode_raw_node_rejects_reserved_disconnect1_code :
  decode_raw_node 0 [false; true; false; true; true] = None.
Proof. reflexivity. Qed.

Example decode_program_bits_unit_with_padding :
  decode_program_bits
    [false; false; true; false; false; true; false; false] =
    Some [RUnit].
Proof. reflexivity. Qed.

Example decode_program_bytes_unit :
  decode_program_bytes [36] = Some [RUnit].
Proof. reflexivity. Qed.

Example decode_program_bytes_rejects_trailing_zero_byte :
  decode_program_bytes [36; 0] = None.
Proof. reflexivity. Qed.

Example decode_structural_program_bytes_unit :
  decode_structural_program_bytes [36] =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example compute_structural_program_cmr_unit :
  compute_structural_program_cmr
    toy_cmr_alg
    {| structural_nodes := [CNode SUnit]; structural_root := 0 |} =
    Some (cmr_unit toy_cmr_alg).
Proof. reflexivity. Qed.

Example decode_structural_program_bytes_with_cmr_unit :
  decode_structural_program_bytes_with_cmr
    toy_cmr_alg
    [36]
    (cmr_unit toy_cmr_alg) =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example decode_structural_program_bytes_with_checked_cmr_unit :
  decode_structural_program_bytes_with_checked_cmr
    zero_cmr_alg
    [36]
    zero_hash256_bits =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example decode_structural_program_bytes_streaming_with_checked_cmr_unit :
  decode_structural_program_bytes_streaming_with_checked_cmr
    zero_cmr_alg
    [36]
    zero_hash256_bits =
    Some {| structural_nodes := [CNode SUnit]; structural_root := 0 |}.
Proof. reflexivity. Qed.

Example decode_structural_program_bytes_rejects_short_expected_cmr :
  decode_structural_program_bytes_with_checked_cmr
    zero_cmr_alg
    [36]
    [false] =
    None.
Proof. reflexivity. Qed.

Example raw_canonical_order_unary :
  raw_canonical_order [RUnit; RInjL 0] = true.
Proof. reflexivity. Qed.

Example raw_canonical_order_shared_child :
  raw_canonical_order [RUnit; RPair 0 0] = true.
Proof. reflexivity. Qed.

Example validate_raw_program_rejects_unused_root_prefix :
  validate_raw_program [RUnit; RUnit] = None.
Proof. reflexivity. Qed.

Example validate_raw_program_rejects_unused_middle_node :
  validate_raw_program [RUnit; RInjL 0; RInjL 0] = None.
Proof. reflexivity. Qed.

Example validate_raw_program_rejects_hidden_root :
  validate_raw_program [RHidden zero_hash256_bits] = None.
Proof. reflexivity. Qed.

Example validate_raw_program_rejects_hidden_noncase_child :
  validate_raw_program [RHidden zero_hash256_bits; RInjL 0] = None.
Proof. reflexivity. Qed.

Example validate_raw_program_rejects_two_hidden_case_children :
  validate_raw_program
    [ RHidden zero_hash256_bits
    ; RHidden (true :: repeat false 255)
    ; RCase 0 1
    ] = None.
Proof. reflexivity. Qed.

Example validate_raw_program_case_hidden_to_assertl :
  validate_raw_program
    [ RUnit
    ; RHidden zero_hash256_bits
    ; RCase 0 1
    ] =
    Some {|
      structural_nodes :=
        [ CNode SUnit
        ; CHidden zero_hash256_bits
        ; CNode (SAssertL 0 zero_hash256_bits)
        ];
      structural_root := 2
    |}.
Proof. reflexivity. Qed.

Example compute_structural_program_cmr_assertl :
  compute_structural_program_cmr
    toy_cmr_alg
    {|
      structural_nodes :=
        [ CNode SUnit
        ; CHidden zero_hash256_bits
        ; CNode (SAssertL 0 zero_hash256_bits)
        ];
      structural_root := 2
    |} =
    Some (cmr_case toy_cmr_alg (cmr_unit toy_cmr_alg) zero_hash256_bits).
Proof. reflexivity. Qed.

Theorem decode_raw_node_jet_roundtrip :
  forall jet rest,
    decode_raw_node 0 (true :: true :: bits_of_elements_jet jet ++ rest) =
      Some (RJet jet, rest).
Proof.
  destruct jet; reflexivity.
Qed.
