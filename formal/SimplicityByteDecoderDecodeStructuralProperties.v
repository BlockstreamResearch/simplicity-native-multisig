From Coq Require Import List Bool Arith Lia.
From MultisigFormal Require Export SimplicityByteDecoderDecodeStructuralCore.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Theorem decode_structural_program_bytes_raw_program :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    exists raw,
      decode_program_bytes bytes = Some raw /\
      validate_raw_program raw = Some program /\
      raw_canonical_order raw = true /\
      raw_program_children_before_from 0 raw.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  exists raw.
  split.
  - unfold decode_program_bytes. exact Hraw.
  - split.
    + exact Hdecode.
    + split.
      * eapply validate_raw_program_canonical_order.
        exact Hdecode.
      * eapply decode_program_bits_raw_children_before.
        exact Hraw.
Qed.

Theorem decode_structural_program_bytes_hidden_cmrs_unique :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    structural_program_hidden_cmrs_unique program.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_hidden_cmrs_unique.
  exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_hidden_cmrs_256 :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    structural_program_hidden_cmrs_256 program.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_hidden_cmrs_256.
  - eapply decode_program_bits_hidden_cmrs_256.
    exact Hraw.
  - exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_streaming_hidden_cmrs_unique :
  forall bytes program,
    decode_structural_program_bytes_streaming bytes = Some program ->
    structural_program_hidden_cmrs_unique program.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes_streaming in Hdecode.
  destruct (decode_program_bytes_streaming bytes) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_hidden_cmrs_unique.
  exact Hdecode.
Qed.

Theorem validate_raw_program_root_is_node :
  forall raw program,
    validate_raw_program raw = Some program ->
    exists root_node,
      nth_error (structural_nodes program) (structural_root program) =
        Some (CNode root_node).
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
  exists root_node. exact Hroot.
Qed.

Theorem validate_raw_program_dag_well_formed :
  forall raw program,
    validate_raw_program raw = Some program ->
    structural_program_dag_well_formed program = true.
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
    (@convert_raw_nodes_backrefs_are_nodes_from
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hconvert)
    as [suffix [Hsuffix_eq Hsuffix_backrefs]].
  simpl in Hsuffix_eq.
  subst converted.
  unfold structural_program_dag_well_formed.
  simpl.
  change
    (match nth_error suffix (pred (length (raw_node :: raw_rest))) with
     | Some (CNode _) =>
         converted_nodes_backrefs_are_nodesb_from [] suffix
     | _ => false
     end = true).
  rewrite Hroot.
  exact Hsuffix_backrefs.
Qed.

Theorem validate_raw_program_no_fail :
  forall raw program,
    raw_program_no_fail raw = true ->
    validate_raw_program raw = Some program ->
    structural_program_no_fail program = true.
Proof.
  intros raw program Hraw_no_fail Hvalidate.
  unfold validate_raw_program in Hvalidate.
  destruct raw as [| raw_node raw_rest]; [discriminate |].
  destruct (raw_canonical_order (raw_node :: raw_rest)) eqn:Hcanonical;
    [| discriminate].
  destruct (convert_raw_nodes (raw_node :: raw_rest) [] [])
    as [[converted seen_hidden] |] eqn:Hconvert; [| discriminate].
  destruct (nth_error converted (pred (length (raw_node :: raw_rest))))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  inversion Hvalidate; subst.
  unfold structural_program_no_fail.
  exact
    (@convert_raw_nodes_preserves_no_fail_from
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hraw_no_fail
      eq_refl
      Hconvert).
Qed.

Theorem validate_raw_program_no_disconnect1 :
  forall raw program,
    raw_program_no_disconnect1 raw = true ->
    validate_raw_program raw = Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros raw program Hraw_no_disconnect1 Hvalidate.
  unfold validate_raw_program in Hvalidate.
  destruct raw as [| raw_node raw_rest]; [discriminate |].
  destruct (raw_canonical_order (raw_node :: raw_rest)) eqn:Hcanonical;
    [| discriminate].
  destruct (convert_raw_nodes (raw_node :: raw_rest) [] [])
    as [[converted seen_hidden] |] eqn:Hconvert; [| discriminate].
  destruct (nth_error converted (pred (length (raw_node :: raw_rest))))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  inversion Hvalidate; subst.
  unfold structural_program_no_disconnect1.
  exact
    (@convert_raw_nodes_preserves_no_disconnect1_from
      (raw_node :: raw_rest)
      []
      []
      converted
      seen_hidden
      Hraw_no_disconnect1
      eq_refl
      Hconvert).
Qed.

Theorem decode_structural_program_bytes_dag_well_formed :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    structural_program_dag_well_formed program = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_dag_well_formed.
  exact Hdecode.
Qed.

Theorem structural_program_dag_well_formed_child_references :
  forall program,
    structural_program_dag_well_formed program = true ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros program Hdag.
  unfold structural_program_child_references_are_backward_nodes.
  intros parent node child Hparent Hchild_in.
  unfold structural_program_dag_well_formed in Hdag.
  destruct (nth_error (structural_nodes program) (structural_root program))
    as [[root_node | hidden_cmr] |] eqn:Hroot; try discriminate.
  pose proof
    (@converted_nodes_backrefs_are_nodesb_from_child_sound
      []
      (structural_nodes program)
      parent
      node
      child
      Hdag
      Hparent
      Hchild_in)
    as [child_node [Hchild_node Hchild_lt]].
  simpl in Hchild_node.
  simpl in Hchild_lt.
  exists child_node.
  split; assumption.
Qed.

Theorem decode_structural_program_bytes_child_references :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    structural_program_child_references_are_backward_nodes program.
Proof.
  intros bytes program Hdecode.
  apply structural_program_dag_well_formed_child_references.
  eapply decode_structural_program_bytes_dag_well_formed.
  exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_no_fail :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    structural_program_no_fail program = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_no_fail.
  - eapply decode_program_bits_no_fail. exact Hraw.
  - exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_no_disconnect1 :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    structural_program_no_disconnect1 program = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  eapply validate_raw_program_no_disconnect1.
  - eapply decode_program_bits_no_disconnect1. exact Hraw.
  - exact Hdecode.
Qed.

Theorem decode_structural_program_bytes_closed_padding :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    program_bytes_closed_padding bytes = true.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  unfold decode_program_bits in Hdecode.
  unfold program_bytes_closed_padding.
  destruct (decode_natural_bound (Some dag_len_max) (bytes_to_bits bytes))
    as [[count bits_after_count] |] eqn:Hcount; [| discriminate].
  destruct (decode_raw_nodes count 0 bits_after_count)
    as [[nodes padding] |] eqn:Hnodes; [| discriminate].
  destruct (close_padding padding) eqn:Hpadding; [| discriminate].
  destruct (validate_raw_program nodes) as [decoded_program |] eqn:Hvalidate;
    [| discriminate].
  reflexivity.
Qed.

Theorem decode_structural_program_bytes_dag_len_bound :
  forall bytes program,
    decode_structural_program_bytes bytes = Some program ->
    length (structural_nodes program) <= dag_len_max.
Proof.
  intros bytes program Hdecode.
  unfold decode_structural_program_bytes in Hdecode.
  unfold decode_structural_program_bits in Hdecode.
  destruct (decode_program_bits (bytes_to_bits bytes)) as [raw |]
    eqn:Hraw; [| discriminate].
  pose proof
    (@validate_raw_program_length raw program Hdecode)
    as Hprogram_length.
  pose proof
    (@decode_program_bits_length_bound
      (bytes_to_bits bytes)
      raw
      Hraw)
    as Hraw_bound.
  rewrite Hprogram_length.
  exact Hraw_bound.
Qed.
