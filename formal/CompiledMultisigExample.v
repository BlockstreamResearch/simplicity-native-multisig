From Coq Require Import List.
From MultisigFormal Require Import
  SimplicityByteDecoder MultisigCertificate MultisigSecurity MultisigSourceBlocks
  CompiledMultisigByteData CompiledMultisigExampleCore.

Import ListNotations.

Theorem compiled_multisig_certificate_source_blocks_if_votes :
  forall (Hash Signature : Type)
         (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : list byte -> Signature -> Hash -> Prop)
         tx current_script_hash total_proposed_outputs current_index
         votes final_input counted,
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
    @multisig_source_blocks_succeed
      (list byte)
      bytes_eqb
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
      compiled_multisig_threshold
      current_index
      compiled_multisig_participant1
      compiled_multisig_participant2
      compiled_multisig_participant3
      votes
      final_input
      counted.
Proof.
  intros Hash Signature Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid tx current_script_hash
    total_proposed_outputs current_index votes final_input counted
    Hvotes_len Hprefix_nonempty Hcurrent_lt Hinputs_available Hcount
    Hthreshold_counted.
  unfold multisig_source_blocks_succeed.
  unfold compiled_multisig_participants in Hcount.
  split.
  - exact compiled_multisig_certificate_static_parameter_checks.
  - split.
    + exact Hvotes_len.
    + split.
      * exact Hprefix_nonempty.
      * split.
        -- exact Hcurrent_lt.
        -- split.
           ++ exact Hinputs_available.
           ++ split.
              ** exact Hcount.
              ** exact Hthreshold_counted.
Qed.

Theorem compiled_multisig_certificate_model_success_if_votes :
  forall (Hash Signature : Type)
         (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : list byte -> Signature -> Hash -> Prop)
         tx current_script_hash total_proposed_outputs current_index
         votes final_input counted,
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
    @multisig_covenant_succeeds
      Hash
      (list byte)
      Signature
      Hash_eq_dec
      hash_words
      participant_message
      vote_taproot_script_hash
      signature_valid
      tx
      current_script_hash
      total_proposed_outputs
      compiled_multisig_threshold
      current_index
      compiled_multisig_participants
      votes.
Proof.
  intros Hash Signature Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid tx current_script_hash
    total_proposed_outputs current_index votes final_input counted
    Hvotes_len Hprefix_nonempty Hcurrent_lt Hinputs_available Hcount
    Hthreshold_counted.
  unfold compiled_multisig_participants.
  eapply (@multisig_source_blocks_imply_model_success
    (list byte)
    bytes_eqb).
  - exact bytes_eqb_false_neq.
  - eapply compiled_multisig_certificate_source_blocks_if_votes.
    + exact Hvotes_len.
    + exact Hprefix_nonempty.
    + exact Hcurrent_lt.
    + exact Hinputs_available.
    + unfold compiled_multisig_participants.
      exact Hcount.
    + exact Hthreshold_counted.
Qed.

Theorem compiled_multisig_certificate_authorizes_threshold_distinct_declared_participants_if_votes :
  forall (Hash Signature : Type)
         (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : list byte -> Signature -> Hash -> Prop)
         tx current_script_hash total_proposed_outputs current_index
         votes final_input counted,
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
        (fun cv => In (counted_participant cv) compiled_multisig_participants)
        counted0 /\
      NoDup (map counted_participant counted0).
Proof.
  intros Hash Signature Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid tx current_script_hash
    total_proposed_outputs current_index votes final_input counted
    Hvotes_len Hprefix_nonempty Hcurrent_lt Hinputs_available Hcount
    Hthreshold_counted.
  eapply (@multisig_success_authorizes_threshold_distinct_declared_participants
    Hash
    (list byte)
    Signature
    Hash_eq_dec
    hash_words
    participant_message
    vote_taproot_script_hash
    signature_valid
    tx
    current_script_hash
    total_proposed_outputs
    compiled_multisig_threshold
    current_index
    compiled_multisig_participants
    votes).
  eapply compiled_multisig_certificate_model_success_if_votes.
  - exact Hvotes_len.
  - exact Hprefix_nonempty.
  - exact Hcurrent_lt.
  - exact Hinputs_available.
  - exact Hcount.
  - exact Hthreshold_counted.
Qed.

Theorem compiled_multisig_certificate_security_property_if_votes :
  forall (Hash Signature : Type)
         (Hash_eq_dec : forall x y : Hash, {x = y} + {x <> y})
         (hash_words : list Hash -> Hash)
         (participant_message : Hash -> Hash -> Hash)
         (vote_taproot_script_hash : Hash -> Signature -> Hash)
         (signature_valid : list byte -> Signature -> Hash -> Prop)
         tx current_script_hash total_proposed_outputs current_index
         votes final_input counted,
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
        (fun cv => In (counted_participant cv) compiled_multisig_participants)
        counted0 /\
      NoDup (map counted_participant counted0) /\
      base =
        hash_words
          (firstn prefix (tx_input_hashes tx)
             ++ firstn total_proposed_outputs (tx_output_hashes tx)) /\
      (forall i,
        i < prefix ->
        nth_error (tx_input_script_hashes tx) i = Some current_script_hash) /\
      (nth_error (tx_input_script_hashes tx) prefix = None \/
       exists h,
         nth_error (tx_input_script_hashes tx) prefix = Some h /\
         h <> current_script_hash).
Proof.
  intros Hash Signature Hash_eq_dec hash_words participant_message
    vote_taproot_script_hash signature_valid tx current_script_hash
    total_proposed_outputs current_index votes final_input counted
    Hvotes_len Hprefix_nonempty Hcurrent_lt Hinputs_available Hcount
    Hthreshold_counted.
  eapply (@multisig_success_security_property
    Hash
    (list byte)
    Signature
    Hash_eq_dec
    hash_words
    participant_message
    vote_taproot_script_hash
    signature_valid
    tx
    current_script_hash
    total_proposed_outputs
    compiled_multisig_threshold
    current_index
    compiled_multisig_participants
    votes).
  eapply compiled_multisig_certificate_model_success_if_votes.
  - exact Hvotes_len.
  - exact Hprefix_nonempty.
  - exact Hcurrent_lt.
  - exact Hinputs_available.
  - exact Hcount.
  - exact Hthreshold_counted.
Qed.

Local Opaque compiled_multisig_certificate.

Theorem compiled_multisig_streaming_bridge_evidence_if_checked_cmr :
  forall alg program,
    compiled_multisig_streaming_checked_program alg = Some program ->
    CompiledMultisigByteCertificateStreamingBridgeEvidence
      alg compiled_multisig_certificate program.
Proof.
  intros alg program Hdecoded.
  unfold compiled_multisig_streaming_checked_program in Hdecoded.
  exact (@check_compiled_multisig_byte_certificate_streaming_bridge_evidence
    alg
    compiled_multisig_certificate
    program
    Hdecoded).
Qed.

Theorem compiled_multisig_decode_evidence_if_some :
  forall program,
    check_compiled_multisig_byte_certificate_without_cmr
      compiled_multisig_certificate = Some program ->
    CompiledMultisigByteCertificateDecodeEvidence
      compiled_multisig_certificate program.
Proof.
  intros program Hdecoded.
  exact (@check_compiled_multisig_byte_certificate_decode_evidence
    compiled_multisig_certificate
    program
    Hdecoded).
Qed.
