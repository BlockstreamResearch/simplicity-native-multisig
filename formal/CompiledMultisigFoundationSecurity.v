From Coq Require Import List.
From MultisigFormal Require Import
  CmrWellFormed CompiledMultisigByteData CompiledMultisigExample
  CompiledMultisigExampleCore CompiledMultisigFoundation
  CompiledMultisigTypedExample
  ElementsJetEnvironment ElementsJetSemantics ElementsJets FoundationCore
  FoundationElementsProviders MultisigCertificate MultisigSecurity
  MultisigTypedCertificate SimplicityByteDecoder.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Artifact security lemmas for the compiled multisig foundation bridge.

  CompiledMultisigFoundation.v proves that the checked compiled bytes have a
  Foundation term.  This module combines that bridge with the source multisig
  security theorem and environment assertion premises.
*)

Theorem compiled_multisig_typed_cmr_checked_artifact_security_if_votes :
  forall alg program
         (Hash Signature : Type)
         (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : list byte -> Signature -> Hash -> Prop)
         tx current_script_hash total_proposed_outputs current_index
         votes final_input counted,
    CmrAlgebraWellFormed alg ->
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits compiled_multisig_certificate) ->
    foundation_elements_term_provider_for_prefixes
      reject_unhandled_type_hooks ->
    length votes = participant_count ->
    1 <= @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash ->
    current_index <
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash ->
    compiled_multisig_threshold +
      @multisig_prefix_count Hash Hash_eq_dec tx current_script_hash <=
      length (tx_input_script_hashes tx) ->
    @CountVotes
      Hash
      (list byte)
      Signature
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
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
      (@multisig_prefix_count Hash Hash_eq_dec tx current_script_hash)
      final_input
      counted ->
    compiled_multisig_threshold <= length counted ->
    exists typed_certificate,
      compiled_multisig_typed_certificate = Some typed_certificate /\
      (exists foundation_term :
        FoundationTermForArrow
          (typed_certificate_root_arrow typed_certificate),
        True) /\
      exists base prefix final_input0 counted0,
        base =
          @base_message
            Hash
            Hash_eq_dec
            hash_words
            tx
            current_script_hash
            total_proposed_outputs /\
        prefix =
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
          prefix
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
            (firstn prefix (tx_input_hashes tx)
               ++ firstn total_proposed_outputs (tx_output_hashes tx)) /\
        (forall i,
          i < prefix ->
          nth_error (tx_input_script_hashes tx) i =
            Some current_script_hash) /\
        (nth_error (tx_input_script_hashes tx) prefix = None \/
         exists h,
           nth_error (tx_input_script_hashes tx) prefix = Some h /\
           h <> current_script_hash).
Proof.
  intros alg program Hash Signature Hash_eq_dec hash_words
    participant_message vote_taproot_script_hash signature_valid tx
    current_script_hash total_proposed_outputs current_index votes
    final_input counted Halg Hdecoded Hcmr Hproviders Hvotes_len
    Hprefix_nonempty Hcurrent_lt Hinputs_available Hcount
    Hthreshold_counted.
  destruct
    (@compiled_multisig_streaming_typed_cmr_checked_root_foundation_term
      alg
      program
      Halg
      Hdecoded
      Hcmr)
    as [typed_certificate [Htyped_certificate Hfoundation_term]].
  {
    eapply foundation_non_core_term_provider_for_prefixes_from_elements_providers.
    exact Hproviders.
  }
  destruct
    (@compiled_multisig_certificate_security_property_if_votes
      Hash
      Signature
      Hash_eq_dec
      hash_words
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      current_script_hash
      total_proposed_outputs
      current_index
      votes
      final_input
      counted
      Hvotes_len
      Hprefix_nonempty
      Hcurrent_lt
      Hinputs_available
      Hcount
      Hthreshold_counted)
    as [base [prefix [final_input0 [counted0 Hsecurity]]]].
  exists typed_certificate.
  split.
  - exact Htyped_certificate.
  - split.
    + exact Hfoundation_term.
    + exists base, prefix, final_input0, counted0.
      exact Hsecurity.
Qed.

Theorem compiled_multisig_typed_cmr_checked_artifact_security_from_environment_asserts_if_votes :
  forall alg program
         (Hash Pubkey Signature Ctx8 : Type)
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
         votes final_input counted prefix carry minimum_inputs_num,
    CmrAlgebraWellFormed alg ->
    compiled_multisig_streaming_typed_decoded_program = Some program ->
    compute_structural_program_cmr alg program =
      Some (certificate_cmr_bits compiled_multisig_certificate) ->
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
    @CountVotes
      Hash
      (list byte)
      Signature
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
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
      counted ->
    compiled_multisig_threshold <= length counted ->
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
  intros alg program Hash Pubkey Signature Ctx8 Hash_eq_dec hash_words
    participant_message vote_taproot_script_hash signature_valid sem Hsem
    env tx current_script_hash total_proposed_outputs current_index votes
    final_input counted prefix carry minimum_inputs_num Halg Hdecoded Hcmr
    Hproviders Henv Hcurrent_index Hprefix Hasserts Hvotes_len Hcount
    Hthreshold_counted.
  pose proof
    (@static_prefix_minimum_asserts_imply_source_block_premises
      Hash
      Pubkey
      Signature
      Ctx8
      (list byte)
      sem
      Hsem
      Hash_eq_dec
      env
      tx
      current_script_hash
      compiled_multisig_threshold
      current_index
      compiled_multisig_participant1
      compiled_multisig_participant2
      compiled_multisig_participant3
      prefix
      carry
      minimum_inputs_num
      Henv
      Hcurrent_index
      Hprefix
      Hasserts)
    as (_Hstatic & Hprefix_nonempty & Hcurrent_lt & Hinputs_available).
  rewrite Hprefix in Hcount.
  eapply compiled_multisig_typed_cmr_checked_artifact_security_if_votes.
  - exact Halg.
  - exact Hdecoded.
  - exact Hcmr.
  - exact Hproviders.
  - exact Hvotes_len.
  - exact Hprefix_nonempty.
  - exact Hcurrent_lt.
  - exact Hinputs_available.
  - exact Hcount.
  - exact Hthreshold_counted.
Qed.
