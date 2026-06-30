From Coq Require Import List Bool Arith.
From MultisigFormal Require Import
  ElementsJets SimplicityByteDecoder TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Source and target types for the Elements jets used by this covenant.

  Source:
    /Volumes/Somebody/Desktop/Simp/simplicity/C/elements/primitiveJetNode.inc
    /Volumes/Somebody/Desktop/Simp/simplicity/C/elements/primitiveInitTy.inc

  This file instantiates only the jet-arrow hook of TypedBridge.v.  It does not
  yet replace the later foundation conversion: FoundationTypes.v connects these
  BridgeType shapes to upstream Simplicity.Ty, while typed Term construction and
  semantic evaluation still remain.
*)

Definition bridge_ty_b : BridgeType :=
  BTSum BTUnit BTUnit.

Fixpoint bridge_word (log_width : nat) : BridgeType :=
  match log_width with
  | 0 => bridge_ty_b
  | S log_width' =>
      let half := bridge_word log_width' in
      BTProd half half
  end.

Definition bridge_ty_u := BTUnit.
Definition bridge_ty_w2 := bridge_word 1.
Definition bridge_ty_w8 := bridge_word 3.
Definition bridge_ty_w16 := bridge_word 4.
Definition bridge_ty_w32 := bridge_word 5.
Definition bridge_ty_w64 := bridge_word 6.
Definition bridge_ty_w128 := bridge_word 7.
Definition bridge_ty_w256 := bridge_word 8.
Definition bridge_ty_w512 := bridge_word 9.
Definition bridge_ty_w1Ki := bridge_word 10.

Definition bridge_ty_mw8 := BTSum bridge_ty_u bridge_ty_w8.
Definition bridge_ty_mw16 := BTSum bridge_ty_u bridge_ty_w16.
Definition bridge_ty_mw32 := BTSum bridge_ty_u bridge_ty_w32.
Definition bridge_ty_mw64 := BTSum bridge_ty_u bridge_ty_w64.
Definition bridge_ty_mw128 := BTSum bridge_ty_u bridge_ty_w128.
Definition bridge_ty_mw256 := BTSum bridge_ty_u bridge_ty_w256.

Definition bridge_ty_pbw32 := BTProd bridge_ty_b bridge_ty_w32.
Definition bridge_ty_pw64w256 := BTProd bridge_ty_w64 bridge_ty_w256.

Definition bridge_ty_pmw16mw8 :=
  BTProd bridge_ty_mw16 bridge_ty_mw8.

Definition bridge_ty_pmw32pmw16mw8 :=
  BTProd bridge_ty_mw32 bridge_ty_pmw16mw8.

Definition bridge_ty_pmw64pmw32pmw16mw8 :=
  BTProd bridge_ty_mw64 bridge_ty_pmw32pmw16mw8.

Definition bridge_ty_pmw128pmw64pmw32pmw16mw8 :=
  BTProd bridge_ty_mw128 bridge_ty_pmw64pmw32pmw16mw8.

Definition bridge_ty_pmw256pmw128pmw64pmw32pmw16mw8 :=
  BTProd bridge_ty_mw256 bridge_ty_pmw128pmw64pmw32pmw16mw8.

Definition bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256 :=
  BTProd
    bridge_ty_pmw256pmw128pmw64pmw32pmw16mw8
    bridge_ty_pw64w256.

Definition bridge_ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w16 :=
  BTProd
    bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
    bridge_ty_w16.

Definition bridge_ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w256 :=
  BTProd
    bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
    bridge_ty_w256.

Definition bridge_ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w512 :=
  BTProd
    bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
    bridge_ty_w512.

Definition bridge_arrow (source target : BridgeType) : BridgeArrow :=
  {| bridge_source := source; bridge_target := target |}.

Definition bridge_word_for_encoded_width
    (encoded_width : nat) : option BridgeType :=
  match encoded_width with
  | 0 => None
  | S log_width => Some (bridge_word log_width)
  end.

Definition word_value_bits_well_formed
    (encoded_width : nat)
    (value_bits : list bool) : bool :=
  match encoded_width with
  | 0 => false
  | S log_width => Nat.eqb (length value_bits) (Nat.pow 2 log_width)
  end.

Definition elements_word_allowed
    (encoded_width : nat)
    (value_bits : list bool)
    (arrow : BridgeArrow) : bool :=
  match bridge_word_for_encoded_width encoded_width with
  | Some target =>
      word_value_bits_well_formed encoded_width value_bits &&
      bridge_arrow_eqb arrow (bridge_arrow bridge_ty_u target)
  | None => false
  end.

Definition elements_disconnect_allowed
    (lhs_arrow rhs_arrow arrow : BridgeArrow) : bool :=
  match bridge_source lhs_arrow with
  | BTProd word_ty source =>
      match bridge_target lhs_arrow with
      | BTProd target_left middle =>
          match bridge_target arrow with
          | BTProd target_left' target_right =>
              bridge_type_eqb word_ty bridge_ty_w256 &&
              bridge_type_eqb source (bridge_source arrow) &&
              bridge_type_eqb target_left target_left' &&
              bridge_type_eqb middle (bridge_source rhs_arrow) &&
              bridge_type_eqb (bridge_target rhs_arrow) target_right
          | _ => false
          end
      | _ => false
      end
  | _ => false
  end.

Definition elements_jet_arrow (j : ElementsJet) : BridgeArrow :=
  match j with
  | JAdd32 =>
      bridge_arrow bridge_ty_w64 bridge_ty_pbw32
  | JBip0340Verify =>
      bridge_arrow bridge_ty_w1Ki bridge_ty_u
  | JBuildTapbranch =>
      bridge_arrow bridge_ty_w512 bridge_ty_w256
  | JBuildTaptweak =>
      bridge_arrow bridge_ty_w512 bridge_ty_w256
  | JCurrentIndex =>
      bridge_arrow bridge_ty_u bridge_ty_w32
  | JCurrentScriptHash =>
      bridge_arrow bridge_ty_u bridge_ty_w256
  | JEq1 =>
      bridge_arrow bridge_ty_w2 bridge_ty_b
  | JEq16 =>
      bridge_arrow bridge_ty_w32 bridge_ty_b
  | JEq256 =>
      bridge_arrow bridge_ty_w512 bridge_ty_b
  | JEq32 =>
      bridge_arrow bridge_ty_w64 bridge_ty_b
  | JIncrement32 =>
      bridge_arrow bridge_ty_w32 bridge_ty_pbw32
  | JInputHash =>
      bridge_arrow bridge_ty_w32 bridge_ty_mw256
  | JInputScriptHash =>
      bridge_arrow bridge_ty_w32 bridge_ty_mw256
  | JLe32 =>
      bridge_arrow bridge_ty_w64 bridge_ty_b
  | JLeftPadLow16_32 =>
      bridge_arrow bridge_ty_w16 bridge_ty_w32
  | JLeftPadLow8_32 =>
      bridge_arrow bridge_ty_w8 bridge_ty_w32
  | JLt32 =>
      bridge_arrow bridge_ty_w64 bridge_ty_b
  | JNumInputs =>
      bridge_arrow bridge_ty_u bridge_ty_w32
  | JOutputHash =>
      bridge_arrow bridge_ty_w32 bridge_ty_mw256
  | JSha256Ctx8Add2 =>
      bridge_arrow
        bridge_ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w16
        bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
  | JSha256Ctx8Add32 =>
      bridge_arrow
        bridge_ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w256
        bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
  | JSha256Ctx8Add64 =>
      bridge_arrow
        bridge_ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w512
        bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
  | JSha256Ctx8Finalize =>
      bridge_arrow
        bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
        bridge_ty_w256
  | JSha256Ctx8Init =>
      bridge_arrow
        bridge_ty_u
        bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
  | JTapdataInit =>
      bridge_arrow
        bridge_ty_u
        bridge_ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
  | JVerify =>
      bridge_arrow bridge_ty_b bridge_ty_u
  end.

Definition type_hooks_with_elements_jets
    (base_hooks : TypeHooks) : TypeHooks := {|
  hook_jet_arrow := elements_jet_arrow;
  hook_witness_allowed := fun _ => true;
  hook_fail_allowed := fun _ _ => false;
  hook_word_allowed := elements_word_allowed;
  hook_disconnect1_allowed := fun _ _ => false;
  hook_disconnect_allowed := elements_disconnect_allowed
|}.

Lemma bridge_type_eqb_refl :
  forall ty,
    bridge_type_eqb ty ty = true.
Proof.
  induction ty as [| left IHleft right IHright
                   | left IHleft right IHright
                   | tag]; simpl.
  - reflexivity.
  - rewrite IHleft, IHright. reflexivity.
  - rewrite IHleft, IHright. reflexivity.
  - apply Nat.eqb_refl.
Qed.

Lemma bridge_arrow_eqb_refl :
  forall arrow,
    bridge_arrow_eqb arrow arrow = true.
Proof.
  intros [source target].
  unfold bridge_arrow_eqb; simpl.
  rewrite bridge_type_eqb_refl, bridge_type_eqb_refl.
  reflexivity.
Qed.

Theorem type_hooks_with_elements_jets_jet_arrow :
  forall base_hooks jet,
    hook_jet_arrow (type_hooks_with_elements_jets base_hooks) jet =
      elements_jet_arrow jet.
Proof.
  reflexivity.
Qed.

Theorem type_hooks_with_elements_jets_word_allowed :
  forall base_hooks encoded_width value_bits arrow,
    hook_word_allowed
      (type_hooks_with_elements_jets base_hooks)
      encoded_width
      value_bits
      arrow =
      elements_word_allowed encoded_width value_bits arrow.
Proof.
  reflexivity.
Qed.

Theorem type_hooks_with_elements_jets_witness_accepts :
  forall base_hooks arrow,
    hook_witness_allowed
      (type_hooks_with_elements_jets base_hooks)
      arrow =
      true.
Proof.
  reflexivity.
Qed.

Theorem type_hooks_with_elements_jets_fail_rejects :
  forall base_hooks entropy_bits arrow,
    hook_fail_allowed
      (type_hooks_with_elements_jets base_hooks)
      entropy_bits
      arrow =
      false.
Proof.
  reflexivity.
Qed.

Theorem type_hooks_with_elements_jets_disconnect_allowed :
  forall base_hooks lhs_arrow rhs_arrow arrow,
    hook_disconnect_allowed
      (type_hooks_with_elements_jets base_hooks)
      lhs_arrow
      rhs_arrow
      arrow =
      elements_disconnect_allowed lhs_arrow rhs_arrow arrow.
Proof.
  reflexivity.
Qed.

Theorem type_hooks_with_elements_jets_disconnect1_rejects :
  forall base_hooks lhs_arrow arrow,
    hook_disconnect1_allowed
      (type_hooks_with_elements_jets base_hooks)
      lhs_arrow
      arrow =
      false.
Proof.
  reflexivity.
Qed.

Theorem elements_jet_typecheck_accepts_declared_arrow :
  forall base_hooks prefix jet,
    typecheck_structural_node
      (type_hooks_with_elements_jets base_hooks)
      prefix
      (SJet jet)
      (elements_jet_arrow jet) = true.
Proof.
  intros base_hooks prefix jet.
  simpl.
  apply bridge_arrow_eqb_refl.
Qed.

Theorem elements_witness_typecheck_accepts_declared_arrow :
  forall base_hooks prefix arrow,
    typecheck_structural_node
      (type_hooks_with_elements_jets base_hooks)
      prefix
      SWitness
      arrow = true.
Proof.
  reflexivity.
Qed.

Theorem elements_word_allowed_sound :
  forall encoded_width value_bits arrow,
    elements_word_allowed encoded_width value_bits arrow = true ->
    exists log_width,
      encoded_width = S log_width /\
      length value_bits = Nat.pow 2 log_width /\
      arrow = bridge_arrow bridge_ty_u (bridge_word log_width).
Proof.
  intros encoded_width value_bits arrow Hallowed.
  destruct encoded_width as [| log_width]; simpl in Hallowed;
    [discriminate |].
  apply andb_true_iff in Hallowed as [Hlength Harrow].
  apply Nat.eqb_eq in Hlength.
  apply bridge_arrow_eqb_true in Harrow.
  exists log_width.
  repeat split; assumption.
Qed.

Theorem elements_disconnect_allowed_sound :
  forall lhs_arrow rhs_arrow arrow,
    elements_disconnect_allowed lhs_arrow rhs_arrow arrow = true ->
    exists source target_left middle target_right,
      bridge_source lhs_arrow = BTProd bridge_ty_w256 source /\
      bridge_target lhs_arrow = BTProd target_left middle /\
      bridge_source rhs_arrow = middle /\
      bridge_target rhs_arrow = target_right /\
      bridge_source arrow = source /\
      bridge_target arrow = BTProd target_left target_right.
Proof.
  intros [lhs_source lhs_target] [rhs_source rhs_target]
    [source target] Hallowed.
  unfold elements_disconnect_allowed in Hallowed.
  simpl in Hallowed.
  destruct lhs_source as [| lhs_source_left lhs_source_right
                         | word_ty source' | lhs_source_tag];
    try discriminate.
  destruct lhs_target as [| lhs_target_left lhs_target_right
                         | target_left middle | lhs_target_tag];
    try discriminate.
  destruct target as [| target_sum_left target_sum_right
                     | target_left' target_right | target_tag];
    try discriminate.
  apply andb_true_iff in Hallowed as [Hprefix Htarget_right].
  apply andb_true_iff in Hprefix as [Hprefix Hmiddle].
  apply andb_true_iff in Hprefix as [Hprefix Htarget_left].
  apply andb_true_iff in Hprefix as [Hword Hsource].
  apply bridge_type_eqb_true in Hword.
  apply bridge_type_eqb_true in Hsource.
  apply bridge_type_eqb_true in Htarget_left.
  apply bridge_type_eqb_true in Hmiddle.
  apply bridge_type_eqb_true in Htarget_right.
  subst.
  exists source, target_left', rhs_source, target_right.
  repeat split; reflexivity.
Qed.

Theorem elements_word_typecheck_accepts_declared_arrow :
  forall base_hooks prefix log_width value_bits,
    length value_bits = Nat.pow 2 log_width ->
    typecheck_structural_node
      (type_hooks_with_elements_jets base_hooks)
      prefix
      (SWord (S log_width) value_bits)
      (bridge_arrow bridge_ty_u (bridge_word log_width)) = true.
Proof.
  intros base_hooks prefix log_width value_bits Hlength.
  simpl.
  unfold elements_word_allowed, word_value_bits_well_formed.
  rewrite Hlength.
  rewrite Nat.eqb_refl.
  apply bridge_arrow_eqb_refl.
Qed.

Theorem elements_disconnect_typecheck_accepts_declared_arrow :
  forall base_hooks prefix lhs rhs source target_left middle target_right,
    typed_prefix_lookup prefix lhs =
      Some (bridge_arrow (BTProd bridge_ty_w256 source)
        (BTProd target_left middle)) ->
    typed_prefix_lookup prefix rhs =
      Some (bridge_arrow middle target_right) ->
    typecheck_structural_node
      (type_hooks_with_elements_jets base_hooks)
      prefix
      (SDisconnect lhs rhs)
      (bridge_arrow source (BTProd target_left target_right)) = true.
Proof.
  intros base_hooks prefix lhs rhs source target_left middle target_right
    Hlhs Hrhs.
  simpl.
  rewrite Hlhs, Hrhs.
  unfold elements_disconnect_allowed.
  simpl.
  repeat rewrite bridge_type_eqb_refl.
  reflexivity.
Qed.
