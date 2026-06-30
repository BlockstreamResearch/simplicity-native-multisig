From Coq Require Import List Bool.
From MultisigFormal Require Import
  CmrWellFormed ElementsJetTypes MultisigCertificate SimplicityByteDecoder
  TypedBridge.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Typed byte-certificate layer for a compiled multisig artifact.

  The byte certificate proves that Coq decoded the actual no-witness program
  bytes and, when supplied a concrete CMR algebra, recomputed the expected CMR.
  This module adds the next certificate field: an exported per-node type table.
  The checker uses ElementsJetTypes.v for the whitelisted Elements jet arrows,
  Simplicity witness admissibility, word type rule, fail rejection, reserved
  one-child disconnect rejection, and the two-child disconnect type rule.
  Witness value decoding and semantic evaluation still wait for the foundation
  bridge.
*)

Record CompiledMultisigTypedByteCertificate := {
  typed_certificate_bytes : CompiledMultisigByteCertificate;
  typed_certificate_types : list (option BridgeArrow);
  typed_certificate_root_arrow : BridgeArrow
}.

Definition typed_certificate_hooks (base_hooks : TypeHooks) : TypeHooks :=
  type_hooks_with_elements_jets base_hooks.

Inductive CompactBridgeTypeDef :=
| CBTDUnit
| CBTDSum (left right : nat)
| CBTDProd (left right : nat)
| CBTDAtom (tag : nat).

Record CompactCompiledMultisigTypedByteCertificate := {
  compact_typed_certificate_bytes : CompiledMultisigByteCertificate;
  compact_bridge_type_defs : list CompactBridgeTypeDef;
  compact_bridge_arrow_defs : list (nat * nat);
  compact_type_table_entries : list (option nat);
  compact_root_arrow_index : nat
}.

Definition decode_compact_bridge_type_def
    (prefix : list BridgeType)
    (type_def : CompactBridgeTypeDef) : option BridgeType :=
  match type_def with
  | CBTDUnit => Some BTUnit
  | CBTDSum left_index right_index =>
      match nth_error prefix left_index, nth_error prefix right_index with
      | Some left_type, Some right_type => Some (BTSum left_type right_type)
      | _, _ => None
      end
  | CBTDProd left_index right_index =>
      match nth_error prefix left_index, nth_error prefix right_index with
      | Some left_type, Some right_type => Some (BTProd left_type right_type)
      | _, _ => None
      end
  | CBTDAtom tag => Some (BTAtom tag)
  end.

Fixpoint decode_compact_bridge_type_defs_from
    (prefix : list BridgeType)
    (type_defs : list CompactBridgeTypeDef) : option (list BridgeType) :=
  match type_defs with
  | [] => Some prefix
  | type_def :: rest =>
      match decode_compact_bridge_type_def prefix type_def with
      | Some decoded_type =>
          decode_compact_bridge_type_defs_from
            (prefix ++ [decoded_type])
            rest
      | None => None
      end
  end.

Definition decode_compact_bridge_type_defs
    (type_defs : list CompactBridgeTypeDef) : option (list BridgeType) :=
  decode_compact_bridge_type_defs_from [] type_defs.

Definition compact_bridge_type_def_atom_free
    (type_def : CompactBridgeTypeDef) : bool :=
  match type_def with
  | CBTDAtom _ => false
  | _ => true
  end.

Definition compact_bridge_type_defs_atom_free
    (type_defs : list CompactBridgeTypeDef) : bool :=
  forallb compact_bridge_type_def_atom_free type_defs.

Lemma forallb_nth_error_true :
  forall A (f : A -> bool) entries index entry,
    forallb f entries = true ->
    nth_error entries index = Some entry ->
    f entry = true.
Proof.
  intros A f entries.
  induction entries as [| head tail IH]; intros index entry Hall Hnth.
  - destruct index; discriminate.
  - simpl in Hall.
    apply andb_true_iff in Hall as [Hhead Htail].
    destruct index as [| index'].
    + simpl in Hnth. inversion Hnth; subst entry. exact Hhead.
    + simpl in Hnth. eapply IH; eauto.
Qed.

Lemma forallb_app_singleton_true :
  forall A (f : A -> bool) entries entry,
    forallb f entries = true ->
    f entry = true ->
    forallb f (entries ++ [entry]) = true.
Proof.
  intros A f entries entry Hentries Hentry.
  rewrite forallb_app.
  simpl.
  rewrite Hentries, Hentry.
  reflexivity.
Qed.

Lemma decode_compact_bridge_type_def_atom_free :
  forall prefix type_def decoded_type,
    forallb bridge_type_atom_free prefix = true ->
    compact_bridge_type_def_atom_free type_def = true ->
    decode_compact_bridge_type_def prefix type_def = Some decoded_type ->
    bridge_type_atom_free decoded_type = true.
Proof.
  intros prefix type_def decoded_type Hprefix Htype_def Hdecode.
  destruct type_def as [| left_index right_index
                       | left_index right_index
                       | tag]; simpl in Htype_def, Hdecode.
  - inversion Hdecode; reflexivity.
  - destruct (nth_error prefix left_index) as [left_type |] eqn:Hleft;
      [| discriminate].
    destruct (nth_error prefix right_index) as [right_type |] eqn:Hright;
      [| discriminate].
    inversion Hdecode; subst decoded_type; simpl.
    rewrite
      (@forallb_nth_error_true BridgeType bridge_type_atom_free
        prefix left_index left_type Hprefix Hleft).
    rewrite
      (@forallb_nth_error_true BridgeType bridge_type_atom_free
        prefix right_index right_type Hprefix Hright).
    reflexivity.
  - destruct (nth_error prefix left_index) as [left_type |] eqn:Hleft;
      [| discriminate].
    destruct (nth_error prefix right_index) as [right_type |] eqn:Hright;
      [| discriminate].
    inversion Hdecode; subst decoded_type; simpl.
    rewrite
      (@forallb_nth_error_true BridgeType bridge_type_atom_free
        prefix left_index left_type Hprefix Hleft).
    rewrite
      (@forallb_nth_error_true BridgeType bridge_type_atom_free
        prefix right_index right_type Hprefix Hright).
    reflexivity.
  - discriminate.
Qed.

Lemma decode_compact_bridge_type_defs_from_atom_free :
  forall type_defs prefix decoded_types,
    forallb bridge_type_atom_free prefix = true ->
    compact_bridge_type_defs_atom_free type_defs = true ->
    decode_compact_bridge_type_defs_from prefix type_defs =
      Some decoded_types ->
    forallb bridge_type_atom_free decoded_types = true.
Proof.
  induction type_defs as [| type_def rest IH];
    intros prefix decoded_types Hprefix Hdefs Hdecode.
  - simpl in Hdecode. inversion Hdecode; subst decoded_types. exact Hprefix.
  - unfold compact_bridge_type_defs_atom_free in Hdefs.
    simpl in Hdefs.
    apply andb_true_iff in Hdefs as [Htype_def Hrest].
    simpl in Hdecode.
    destruct (decode_compact_bridge_type_def prefix type_def)
      as [decoded_type |] eqn:Hdecoded_type; [| discriminate].
    eapply IH.
    + apply forallb_app_singleton_true.
      * exact Hprefix.
      * eapply decode_compact_bridge_type_def_atom_free; eauto.
    + exact Hrest.
    + exact Hdecode.
Qed.

Theorem decode_compact_bridge_type_defs_atom_free :
  forall type_defs decoded_types,
    compact_bridge_type_defs_atom_free type_defs = true ->
    decode_compact_bridge_type_defs type_defs = Some decoded_types ->
    forallb bridge_type_atom_free decoded_types = true.
Proof.
  intros type_defs decoded_types Hdefs Hdecode.
  unfold decode_compact_bridge_type_defs in Hdecode.
  eapply (@decode_compact_bridge_type_defs_from_atom_free
    type_defs [] decoded_types).
  - reflexivity.
  - exact Hdefs.
  - exact Hdecode.
Qed.

Definition decode_compact_bridge_arrow_def
    (types : list BridgeType)
    (arrow_def : nat * nat) : option BridgeArrow :=
  match nth_error types (fst arrow_def), nth_error types (snd arrow_def) with
  | Some source, Some target =>
      Some {| bridge_source := source; bridge_target := target |}
  | _, _ => None
  end.

Fixpoint decode_compact_bridge_arrow_defs
    (types : list BridgeType)
    (arrow_defs : list (nat * nat)) : option (list BridgeArrow) :=
  match arrow_defs with
  | [] => Some []
  | arrow_def :: rest =>
      match decode_compact_bridge_arrow_def types arrow_def,
            decode_compact_bridge_arrow_defs types rest with
      | Some arrow, Some arrows => Some (arrow :: arrows)
      | _, _ => None
      end
  end.

Definition decode_compact_type_table_entry
    (arrows : list BridgeArrow)
    (entry : option nat) : option (option BridgeArrow) :=
  match entry with
  | Some arrow_index =>
      match nth_error arrows arrow_index with
      | Some arrow => Some (Some arrow)
      | None => None
      end
  | None => Some None
  end.

Definition typed_byte_certificate_atom_free
    (certificate : CompiledMultisigTypedByteCertificate) : bool :=
  forallb
    option_bridge_arrow_atom_free
    (typed_certificate_types certificate) &&
  bridge_arrow_atom_free (typed_certificate_root_arrow certificate).

Lemma decode_compact_bridge_arrow_def_atom_free :
  forall types arrow_def decoded_arrow,
    forallb bridge_type_atom_free types = true ->
    decode_compact_bridge_arrow_def types arrow_def = Some decoded_arrow ->
    bridge_arrow_atom_free decoded_arrow = true.
Proof.
  intros types [source_index target_index] decoded_arrow Htypes Hdecode.
  unfold decode_compact_bridge_arrow_def in Hdecode.
  simpl in Hdecode.
  destruct (nth_error types source_index) as [source |] eqn:Hsource;
    destruct (nth_error types target_index) as [target |] eqn:Htarget;
    try discriminate.
  destruct decoded_arrow as [decoded_source decoded_target].
  simpl in Hdecode.
  inversion Hdecode; subst decoded_source decoded_target.
  unfold bridge_arrow_atom_free; simpl.
  rewrite
    (@forallb_nth_error_true BridgeType bridge_type_atom_free
      types source_index source Htypes Hsource).
  rewrite
    (@forallb_nth_error_true BridgeType bridge_type_atom_free
      types target_index target Htypes Htarget).
  reflexivity.
Qed.

Lemma decode_compact_bridge_arrow_defs_atom_free :
  forall types arrow_defs decoded_arrows,
    forallb bridge_type_atom_free types = true ->
    decode_compact_bridge_arrow_defs types arrow_defs = Some decoded_arrows ->
    forallb bridge_arrow_atom_free decoded_arrows = true.
Proof.
  induction arrow_defs as [| arrow_def rest IH];
    intros decoded_arrows Htypes Hdecode.
  - simpl in Hdecode. inversion Hdecode; reflexivity.
  - simpl in Hdecode.
    destruct (decode_compact_bridge_arrow_def types arrow_def)
      as [decoded_arrow |] eqn:Hdecoded_arrow; [| discriminate].
    destruct (decode_compact_bridge_arrow_defs types rest)
      as [decoded_rest |] eqn:Hdecoded_rest; [| discriminate].
    inversion Hdecode; subst decoded_arrows.
    simpl.
    rewrite
      (@decode_compact_bridge_arrow_def_atom_free
        types arrow_def decoded_arrow Htypes Hdecoded_arrow).
    rewrite (@IH decoded_rest Htypes eq_refl).
    reflexivity.
Qed.

Lemma decode_compact_type_table_entry_atom_free :
  forall arrows entry decoded_entry,
    forallb bridge_arrow_atom_free arrows = true ->
    decode_compact_type_table_entry arrows entry = Some decoded_entry ->
    option_bridge_arrow_atom_free decoded_entry = true.
Proof.
  intros arrows entry decoded_entry Harrows Hdecode.
  destruct entry as [arrow_index |]; simpl in Hdecode.
  - destruct (nth_error arrows arrow_index) as [arrow |] eqn:Harrow;
      [| discriminate].
    inversion Hdecode; subst decoded_entry; simpl.
    eapply forallb_nth_error_true; eauto.
  - inversion Hdecode; reflexivity.
Qed.

Fixpoint decode_compact_type_table_entries
    (arrows : list BridgeArrow)
    (entries : list (option nat)) : option (list (option BridgeArrow)) :=
  match entries with
  | [] => Some []
  | entry :: rest =>
      match decode_compact_type_table_entry arrows entry,
            decode_compact_type_table_entries arrows rest with
      | Some decoded_entry, Some decoded_entries =>
          Some (decoded_entry :: decoded_entries)
      | _, _ => None
      end
  end.

Lemma decode_compact_type_table_entries_atom_free :
  forall arrows entries decoded_entries,
    forallb bridge_arrow_atom_free arrows = true ->
    decode_compact_type_table_entries arrows entries = Some decoded_entries ->
    forallb option_bridge_arrow_atom_free decoded_entries = true.
Proof.
  induction entries as [| entry rest IH];
    intros decoded_entries Harrows Hdecode.
  - simpl in Hdecode. inversion Hdecode; reflexivity.
  - simpl in Hdecode.
    destruct (decode_compact_type_table_entry arrows entry)
      as [decoded_entry |] eqn:Hdecoded_entry; [| discriminate].
    destruct (decode_compact_type_table_entries arrows rest)
      as [decoded_rest |] eqn:Hdecoded_rest; [| discriminate].
    inversion Hdecode; subst decoded_entries.
    simpl.
    rewrite
      (@decode_compact_type_table_entry_atom_free
        arrows entry decoded_entry Harrows Hdecoded_entry).
    rewrite (@IH decoded_rest Harrows eq_refl).
    reflexivity.
Qed.

Definition expand_compact_typed_certificate
    (certificate : CompactCompiledMultisigTypedByteCertificate) :
    option CompiledMultisigTypedByteCertificate :=
  match decode_compact_bridge_type_defs
          (compact_bridge_type_defs certificate) with
  | Some types =>
      match decode_compact_bridge_arrow_defs
              types
              (compact_bridge_arrow_defs certificate) with
      | Some arrows =>
          match decode_compact_type_table_entries
                  arrows
                  (compact_type_table_entries certificate),
                nth_error arrows (compact_root_arrow_index certificate) with
          | Some type_table, Some root_arrow =>
              Some {|
                typed_certificate_bytes :=
                  compact_typed_certificate_bytes certificate;
                typed_certificate_types := type_table;
                typed_certificate_root_arrow := root_arrow
              |}
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem expand_compact_typed_certificate_atom_free :
  forall certificate typed_certificate,
    compact_bridge_type_defs_atom_free
      (compact_bridge_type_defs certificate) = true ->
    expand_compact_typed_certificate certificate = Some typed_certificate ->
    typed_byte_certificate_atom_free typed_certificate = true.
Proof.
  intros certificate typed_certificate Htype_defs Hexpand.
  unfold expand_compact_typed_certificate in Hexpand.
  destruct (decode_compact_bridge_type_defs
              (compact_bridge_type_defs certificate)) as [types |]
    eqn:Htypes; [| discriminate].
  destruct (decode_compact_bridge_arrow_defs
              types
              (compact_bridge_arrow_defs certificate)) as [arrows |]
    eqn:Harrows; [| discriminate].
  destruct (decode_compact_type_table_entries
              arrows
              (compact_type_table_entries certificate)) as [type_table |]
    eqn:Htype_table; [| discriminate].
  destruct (nth_error arrows (compact_root_arrow_index certificate))
    as [root_arrow |] eqn:Hroot; [| discriminate].
  inversion Hexpand; subst typed_certificate.
  unfold typed_byte_certificate_atom_free; simpl.
  assert (Htypes_atom_free : forallb bridge_type_atom_free types = true).
  {
    eapply decode_compact_bridge_type_defs_atom_free; eauto.
  }
  assert (Harrows_atom_free : forallb bridge_arrow_atom_free arrows = true).
  {
    eapply decode_compact_bridge_arrow_defs_atom_free; eauto.
  }
  rewrite
    (@decode_compact_type_table_entries_atom_free
      arrows
      (compact_type_table_entries certificate)
      type_table
      Harrows_atom_free
      Htype_table).
  rewrite
    (@forallb_nth_error_true BridgeArrow bridge_arrow_atom_free
      arrows
      (compact_root_arrow_index certificate)
      root_arrow
      Harrows_atom_free
      Hroot).
  reflexivity.
Qed.
