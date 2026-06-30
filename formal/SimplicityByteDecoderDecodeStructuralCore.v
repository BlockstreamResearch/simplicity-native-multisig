From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderDecodeRawProofs.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Definition decode_program_bytes (bytes : list byte) :
    option (list RawNode) :=
  decode_program_bits (bytes_to_bits bytes).

Definition decode_structural_program_bits (bits : list bool) :
    option StructuralProgram :=
  match decode_program_bits bits with
  | Some raw => validate_raw_program raw
  | None => None
  end.

Definition decode_structural_program_bytes (bytes : list byte) :
    option StructuralProgram :=
  decode_structural_program_bits (bytes_to_bits bytes).

Lemma convert_raw_nodes_length :
  forall raw converted seen_hidden converted' seen_hidden',
    convert_raw_nodes raw converted seen_hidden =
      Some (converted', seen_hidden') ->
    length converted' = length converted + length raw.
Proof.
  induction raw as [| raw_node raw_rest IH];
    intros converted seen_hidden converted' seen_hidden' Hconvert;
    simpl in Hconvert.
  - inversion Hconvert; subst. rewrite Nat.add_0_r. reflexivity.
  - destruct (convert_raw_node converted seen_hidden raw_node)
      as [[converted_node seen_hidden_next] |] eqn:Hnode;
      [| discriminate].
    specialize
      (IH (converted ++ [converted_node]) seen_hidden_next
        converted' seen_hidden' Hconvert).
    rewrite IH.
    rewrite length_app.
    simpl.
    rewrite <- Nat.add_assoc.
    reflexivity.
Qed.

Theorem validate_raw_program_length :
  forall raw program,
    validate_raw_program raw = Some program ->
    length (structural_nodes program) = length raw.
Proof.
  intros raw program Hvalidate.
  unfold validate_raw_program in Hvalidate.
  destruct raw as [| raw_node raw_rest]; [discriminate |].
  destruct (raw_canonical_order (raw_node :: raw_rest)) eqn:Hcanonical;
    [| discriminate].
  destruct (convert_raw_nodes (raw_node :: raw_rest) [] [])
    as [[converted seen_hidden] |] eqn:Hconvert; [| discriminate].
  destruct (nth_error converted (pred (length (raw_node :: raw_rest))))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  inversion Hvalidate; subst; simpl.
  pose proof
    (@convert_raw_nodes_length
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hconvert)
    as Hlength.
  simpl in Hlength. exact Hlength.
Qed.

Theorem validate_raw_program_canonical_order :
  forall raw program,
    validate_raw_program raw = Some program ->
    raw_canonical_order raw = true.
Proof.
  intros raw program Hvalidate.
  unfold validate_raw_program in Hvalidate.
  destruct raw as [| raw_node raw_rest]; [discriminate |].
  destruct (raw_canonical_order (raw_node :: raw_rest)) eqn:Hcanonical;
    [reflexivity | discriminate].
Qed.

Theorem validate_raw_program_hidden_cmrs_unique :
  forall raw program,
    validate_raw_program raw = Some program ->
    structural_program_hidden_cmrs_unique program.
Proof.
  intros raw program Hvalidate.
  unfold validate_raw_program in Hvalidate.
  destruct raw as [| raw_node raw_rest]; [discriminate |].
  destruct (raw_canonical_order (raw_node :: raw_rest)) eqn:Hcanonical;
    [| discriminate].
  destruct (convert_raw_nodes (raw_node :: raw_rest) [] [])
    as [[converted seen_hidden] |] eqn:Hconvert; [| discriminate].
  destruct (nth_error converted (pred (length (raw_node :: raw_rest))))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  inversion Hvalidate; subst.
  pose proof
    (@convert_raw_nodes_preserves_seen_hidden_NoDup
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      (NoDup_nil _)
      Hconvert)
    as Hseen_nodup.
  pose proof
    (@convert_raw_nodes_hidden_seen_relation
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hconvert)
    as [suffix [Hconverted Hseen]].
  simpl in Hconverted.
  subst converted.
  simpl in Hseen.
  rewrite app_nil_r in Hseen.
  subst seen_hidden.
  unfold structural_program_hidden_cmrs_unique.
  unfold structural_program_hidden_cmrs.
  simpl.
  pose proof
    (@NoDup_rev (list bool)
      (rev (converted_nodes_hidden_cmrs suffix))
      Hseen_nodup)
    as Hnodup_original.
  rewrite rev_involutive in Hnodup_original.
  exact Hnodup_original.
Qed.

Theorem validate_raw_program_hidden_cmrs_256 :
  forall raw program,
    raw_program_hidden_cmrs_256 raw ->
    validate_raw_program raw = Some program ->
    structural_program_hidden_cmrs_256 program.
Proof.
  intros raw program Hraw_hidden Hvalidate.
  unfold validate_raw_program in Hvalidate.
  destruct raw as [| raw_node raw_rest]; [discriminate |].
  destruct (raw_canonical_order (raw_node :: raw_rest)) eqn:Hcanonical;
    [| discriminate].
  destruct (convert_raw_nodes (raw_node :: raw_rest) [] [])
    as [[converted seen_hidden] |] eqn:Hconvert; [| discriminate].
  destruct (nth_error converted (pred (length (raw_node :: raw_rest))))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  inversion Hvalidate; subst.
  pose proof
    (@convert_raw_nodes_preserves_seen_hidden_256
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hraw_hidden
      (Forall_nil _)
      Hconvert)
    as Hseen_hidden.
  pose proof
    (@convert_raw_nodes_hidden_seen_relation
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hconvert)
    as [suffix [Hconverted Hseen]].
  simpl in Hconverted.
  subst converted.
  simpl in Hseen.
  rewrite app_nil_r in Hseen.
  subst seen_hidden.
  unfold structural_program_hidden_cmrs_256.
  unfold structural_program_hidden_cmrs.
  simpl.
  pose proof
    (@Forall_rev (list bool)
      cmr_bits_length_256
      (rev (converted_nodes_hidden_cmrs suffix))
      Hseen_hidden)
    as Hhidden_original.
  rewrite rev_involutive in Hhidden_original.
  exact Hhidden_original.
Qed.
