(*
  CompiledMultisigRealSecurity.v — G5 completion: the strongest byte-level
  artifact theorems, with the checked-run premise DISCHARGED under the concrete
  self-contained SHA-256 CMR algebra.

  Every prior artifact-security theorem in the tree is conditional on
  [compiled_multisig_streaming_typed_checked_program alg ... = Some program]
  for an abstract (or foundation-shaped) CmrAlgebra.  This file closes that
  last gap: it proves the checked run SUCCEEDS under [simplicity_cmr_algebra]
  (Sha256Core.v + SimplicityCmrSha.v — validated against FIPS 180-4 and
  rust-simplicity's BITS constants), by reassembling the already-proven
  decode, type-check and real-CMR facts.  No exporter trust, no abstract
  algebra, no assumed checked run: the only remaining premises of the final
  security theorem are the semantic ones (jet semantics, environment/tx
  relation, executed votes, term providers).

  PROOF-STYLE CONSTRAINT (memory): do NOT enable [Set Implicit Arguments]/
  [Set Strict Implicit] here, and materialize applied lemmas with
  [pose proof ... as H] before [exact H] — see
  CompiledMultisigFoundationCmrEvidence.v for the Qed memory blowup this
  avoids.  Reductions in this file are restricted to [lazy beta iota] (plus
  one tiny [lazy] on the 32-byte CMR-bits well-formedness check) so no proof
  ever re-runs the byte decoder.
*)

From Coq Require Import List Bool.
From MultisigFormal Require Import
  CmrWellFormed CompiledMultisigByteData CompiledMultisigExample
  CompiledMultisigExampleCore CompiledMultisigFoundation
  CompiledMultisigFoundationSecurity CompiledMultisigRealCmr
  CompiledMultisigRealCmrChecked CompiledMultisigTypedExample
  ElementsJetEnvironment ElementsJetSemantics ElementsJets FoundationCore
  FoundationElementsProviders MultisigCertificate MultisigSecurity
  MultisigTypedCertificate SimplicityByteDecoder SimplicityCmrAlgebra
  SimplicityCmrAlgebraWf TypedBridge.

Import ListNotations.

(* Expansion preserves the underlying byte certificate. *)
Lemma expand_compact_typed_certificate_bytes :
  forall certificate typed_certificate,
    expand_compact_typed_certificate certificate = Some typed_certificate ->
    typed_certificate_bytes typed_certificate =
      compact_typed_certificate_bytes certificate.
Proof.
  intros certificate typed_certificate Hexpand.
  unfold expand_compact_typed_certificate in Hexpand.
  destruct (decode_compact_bridge_type_defs
              (compact_bridge_type_defs certificate))
    as [types |]; [| discriminate].
  destruct (decode_compact_bridge_arrow_defs
              types (compact_bridge_arrow_defs certificate))
    as [arrows |]; [| discriminate].
  destruct (decode_compact_type_table_entries
              arrows (compact_type_table_entries certificate))
    as [type_table |]; [| discriminate].
  destruct (nth_error arrows (compact_root_arrow_index certificate))
    as [root_arrow |]; [| discriminate].
  inversion Hexpand.
  reflexivity.
Qed.

(* The exported CMR bits pass the 256-bit gate (32 concrete bytes). *)
Example compiled_multisig_certificate_cmr_bits_require :
  require_cmr_bits (certificate_cmr_bits compiled_multisig_certificate) =
    Some (certificate_cmr_bits compiled_multisig_certificate).
Proof.
  lazy.
  reflexivity.
Qed.

(*
  THE DISCHARGED CHECKED RUN: the full streaming typed+CMR certificate checker
  succeeds on the deployed compact certificate under the concrete SHA-256
  algebra.  Assembled from compiled_multisig_real_checked_cmr (real CMR),
  compiled_multisig_streaming_typed_decoded_program_is_some (decode+types) and
  compiled_multisig_typed_certificate_expands — no new heavy computation.
*)
Theorem compiled_multisig_real_typed_checked_program :
  exists program,
    compiled_multisig_streaming_typed_checked_program
      simplicity_cmr_algebra reject_unhandled_type_hooks = Some program.
Proof.
  (* Real-CMR facts for the decoded program. *)
  destruct compiled_multisig_real_checked_cmr as [program [Hdec_raw Hcmr]].
  pose proof Hdec_raw as Hdecode.
  unfold compiled_multisig_streaming_structural_program in Hdecode.
  (* The compact certificate expands. *)
  pose proof compiled_multisig_typed_certificate_expands as Hexp_bool.
  unfold compiled_multisig_typed_certificate in Hexp_bool.
  destruct (expand_compact_typed_certificate
              compiled_multisig_compact_typed_certificate)
    as [tc |] eqn:Hexpand; [| discriminate].
  clear Hexp_bool.
  (* The typed without-CMR checker succeeds; extract its components. *)
  pose proof compiled_multisig_streaming_typed_decoded_program_is_some
    as Hty_bool.
  unfold compiled_multisig_streaming_typed_decoded_program in Hty_bool.
  unfold check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr
    in Hty_bool.
  rewrite Hexpand in Hty_bool.
  destruct (check_compiled_multisig_typed_byte_certificate_streaming_without_cmr
              reject_unhandled_type_hooks tc)
    as [p1 |] eqn:Hty_checked; [| discriminate].
  clear Hty_bool.
  apply check_compiled_multisig_typed_byte_certificate_streaming_without_cmr_sound
    in Hty_checked.
  destruct Hty_checked as [Hbytes1 Htypedchk].
  (* The expanded certificate carries the deployed bytes. *)
  assert (Hbytes_tc :
    typed_certificate_bytes tc = compiled_multisig_certificate).
  {
    pose proof
      (@expand_compact_typed_certificate_bytes
        compiled_multisig_compact_typed_certificate
        tc
        Hexpand) as Hb.
    rewrite Hb.
    exact compiled_multisig_compact_typed_certificate_bytes.
  }
  rewrite Hbytes_tc in Hbytes1.
  apply check_compiled_multisig_byte_certificate_streaming_without_cmr_sound
    in Hbytes1.
  destruct Hbytes1 as [Hshape Hdec1].
  (* Both decode facts name the same program. *)
  assert (Hp1 : p1 = program).
  {
    rewrite Hdecode in Hdec1.
    injection Hdec1 as Hp1.
    exact (eq_sym Hp1).
  }
  subst p1.
  (* The checked CMR verification succeeds under the real algebra. *)
  assert (Hverify :
    verify_structural_program_cmr_checked
      simplicity_cmr_algebra
      program
      (certificate_cmr_bits compiled_multisig_certificate) = true).
  {
    unfold verify_structural_program_cmr_checked.
    rewrite compiled_multisig_certificate_cmr_bits_require.
    rewrite Hcmr.
    apply bits_eqb_refl.
  }
  (* The byte-level checker (shape + decode + checked CMR) succeeds. *)
  assert (Hbyte_checked :
    check_compiled_multisig_byte_certificate_streaming
      simplicity_cmr_algebra
      compiled_multisig_certificate = Some program).
  {
    unfold check_compiled_multisig_byte_certificate_streaming.
    rewrite Hshape.
    unfold decode_structural_program_bytes_streaming_with_checked_cmr.
    rewrite Hdecode.
    rewrite Hverify.
    reflexivity.
  }
  (* Assemble the full compact typed checker run. *)
  exists program.
  unfold compiled_multisig_streaming_typed_checked_program.
  unfold check_compiled_multisig_compact_typed_byte_certificate_streaming.
  rewrite Hexpand.
  lazy beta iota.
  unfold check_compiled_multisig_typed_byte_certificate_streaming.
  rewrite Hbytes_tc.
  rewrite Hbyte_checked.
  lazy beta iota.
  rewrite Htypedchk.
  reflexivity.
Qed.

(*
  The deployed artifact has a Foundation term, under the concrete SHA-256
  algebra, conditional only on the elements term-provider family.
*)
Theorem compiled_multisig_real_root_foundation_term :
  foundation_elements_term_provider_for_prefixes
    reject_unhandled_type_hooks ->
  exists typed_certificate,
    compiled_multisig_typed_certificate = Some typed_certificate /\
    exists foundation_term :
      FoundationTermForArrow
        (typed_certificate_root_arrow typed_certificate),
      True.
Proof.
  intros Hproviders.
  destruct compiled_multisig_real_typed_checked_program
    as [program Hchecked].
  pose proof
    (@compiled_multisig_streaming_typed_checked_root_foundation_term_with_elements_providers
      simplicity_cmr_algebra
      program
      Hchecked
      Hproviders) as Hterm.
  exact Hterm.
Qed.

(*
  THE STRONGEST BYTE-LEVEL ARTIFACT SECURITY THEOREM.

  Identical conclusion to
  compiled_multisig_streaming_typed_checked_artifact_security_from_executed_votes,
  but with the CmrAlgebra fixed to the concrete self-contained SHA-256 algebra
  and the checked-run premise discharged by the closed computation above.
  Remaining premises are purely semantic.
*)
Theorem compiled_multisig_real_artifact_security_from_executed_votes :
  forall (Hash Pubkey Signature Ctx8 : Type)
         (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : list byte -> Signature -> Hash -> Prop)
         (sem : ElementsJetSemantics Hash Pubkey Signature Ctx8 (list byte))
         (Hsem :
           @ElementsJetSemanticsSpec
             Hash Pubkey Signature Ctx8 (list byte) sem)
         env tx current_script_hash total_proposed_outputs current_index
         votes final_input counted_count counted prefix carry
         minimum_inputs_num,
    foundation_elements_term_provider_for_prefixes
      reject_unhandled_type_hooks ->
    ElementsEnvTxRelation sem env tx current_script_hash ->
    current_index = env_current_index env ->
    prefix =
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash ->
    static_prefix_minimum_asserts_succeed
      sem
      compiled_multisig_threshold
      compiled_multisig_participant1
      compiled_multisig_participant2
      compiled_multisig_participant3
      env
      prefix
      carry
      minimum_inputs_num ->
    length votes = participant_count ->
    ElementsVoteSlotsExecution
      sem
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
        (list byte)
        Signature
        compiled_multisig_participants
        votes)
      prefix
      final_input
      counted_count
      counted ->
    vote_threshold_assert_succeeds
      sem
      compiled_multisig_threshold
      counted_count ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      (exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True) /\
      exists base prefix0 final_input0 counted0,
        base =
          @base_message
            Hash
            Hash_eq_dec
            hash_words
            tx
            current_script_hash
            total_proposed_outputs /\
        prefix0 =
          @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash /\
        compiled_multisig_threshold <= length counted0 /\
        @CountVotes
          Hash
          (list byte)
          Signature
          participant_message
          vote_taproot_script_hash
          signature_valid
          tx
          base
          (@vote_slots
            Hash
            (list byte)
            Signature
            compiled_multisig_participants
            votes)
          prefix0
          final_input0
          counted0 /\
        Forall
          (@counted_vote_valid
            Hash
            (list byte)
            Signature
            participant_message
            vote_taproot_script_hash
            signature_valid
            tx)
          counted0 /\
        Forall
          (fun cv =>
            In (counted_participant cv) compiled_multisig_participants)
          counted0 /\
        NoDup (map counted_participant counted0) /\
        base =
          hash_words
            (firstn prefix0 (tx_input_hashes tx)
               ++ firstn total_proposed_outputs (tx_output_hashes tx)) /\
        (forall i,
          i < prefix0 ->
          nth_error (tx_input_script_hashes tx) i =
            Some current_script_hash) /\
        (nth_error (tx_input_script_hashes tx) prefix0 = None \/
         exists h,
           nth_error (tx_input_script_hashes tx) prefix0 = Some h /\
           h <> current_script_hash).
Proof.
  intros Hash Pubkey Signature Ctx8 Hash_eq_dec hash_words
    participant_message vote_taproot_script_hash signature_valid sem Hsem
    env tx current_script_hash total_proposed_outputs current_index votes
    final_input counted_count counted prefix carry minimum_inputs_num
    Hproviders Henv Hcurrent_index Hprefix Hasserts Hvotes_len Hexec
    Hthreshold.
  destruct compiled_multisig_real_typed_checked_program
    as [program Hchecked].
  pose proof
    (@compiled_multisig_streaming_typed_checked_artifact_security_from_executed_votes
      simplicity_cmr_algebra
      program
      Hash
      Pubkey
      Signature
      Ctx8
      Hash_eq_dec
      hash_words
      participant_message
      vote_taproot_script_hash
      signature_valid
      sem
      Hsem
      env
      tx
      current_script_hash
      total_proposed_outputs
      current_index
      votes
      final_input
      counted_count
      counted
      prefix
      carry
      minimum_inputs_num
      Hchecked
      Hproviders
      Henv
      Hcurrent_index
      Hprefix
      Hasserts
      Hvotes_len
      Hexec
      Hthreshold) as Hsecurity.
  exact Hsecurity.
Qed.
