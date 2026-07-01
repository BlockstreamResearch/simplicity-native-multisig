From Coq Require Import List.
From MultisigFormal Require Import
  CompiledMultisigByteData CompiledMultisigExample
  CompiledMultisigExampleCore CompiledMultisigFoundationSecurity
  CompiledMultisigTypedExample ElementsJetEnvironment
  ElementsJetSemantics ElementsJets FoundationCmrAlgebra FoundationCore
  FoundationElementsProviders MultisigSecurity
  MultisigTypedCertificate MultisigTypedCertificateExamples
  SimplicityByteDecoder.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Security theorem specialized to the foundation-shaped CMR adapter.

  This is still conditional on the checked-program run succeeding.  The point of
  this layer is to remove the arbitrary-CmrAlgebra surface from the strongest
  artifact theorem: the remaining executable CMR obligation must instantiate
  FoundationCmrOps with the upstream Simplicity.Digest/MerkleRoot operations and
  run the checker with that concrete adapter.
*)

Theorem compiled_multisig_foundation_cmr_checked_artifact_security_from_executed_votes :
  forall ops program
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
         votes final_input counted_count counted prefix carry
         minimum_inputs_num,
    compiled_multisig_streaming_typed_checked_program
      (foundation_elements_cmr_algebra ops)
      reject_unhandled_type_hooks = Some program ->
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
  intros ops program Hash Pubkey Signature Ctx8 Hash_eq_dec hash_words
    participant_message vote_taproot_script_hash signature_valid sem Hsem
    env tx current_script_hash total_proposed_outputs current_index votes
    final_input counted_count counted prefix carry minimum_inputs_num Hchecked
    Hproviders Henv Hcurrent_index Hprefix Hasserts Hvotes_len Hexec
    Hthreshold.
  eapply
    (@compiled_multisig_streaming_typed_checked_artifact_security_from_executed_votes
      (foundation_elements_cmr_algebra ops)
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
      minimum_inputs_num).
  - exact Hchecked.
  - exact Hproviders.
  - exact Henv.
  - exact Hcurrent_index.
  - exact Hprefix.
  - exact Hasserts.
  - exact Hvotes_len.
  - exact Hexec.
  - exact Hthreshold.
Qed.
