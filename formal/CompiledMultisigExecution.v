(*
  CompiledMultisigExecution.v — G4 executable-semantics evidence: the deployed
  multisig byte artifact, decoded by the audited byte decoder and EXECUTED
  inside Coq by SimplicityStructuralEval.v under the concrete jet
  interpretation of ElementsConcreteJets.v, exhibits exactly the multisig
  policy behavior on concrete transaction scenarios:

  - it ACCEPTS an honest scenario: two votes whose signatures are valid for
    the participants' compiled-in keys over the correctly reconstructed
    participant message (real SHA-256 over the multisig input hash and the
    proposed output hash), with each vote committed on-chain through the
    taproot vote-script construction; and
  - it REJECTS, on the same or minimally perturbed scenarios:
      * when no signature is valid,
      * when only one vote is valid (below the compiled-in threshold of 2),
      * when a vote's on-chain taproot commitment is absent, and
      * when the proposed outputs are tampered with (so every signature
        covers a different base message).

  Every theorem is a closed computation over the REAL deployed bytes
  (cert_program_bytes of the exported certificate): no exporter trust, no
  hand-written model of the program.  The signature table plays exactly the
  role of the abstract [signature_valid] predicate of the security model;
  elliptic-curve arithmetic is not interpreted (see ElementsConcreteJets.v).

  The evaluation results are EValue/EFail in every scenario — the evaluator
  never reaches the EStuck structural-error state on the deployed program.

  PROOF-STYLE CONSTRAINT (memory): no [Set Implicit Arguments]/[Set Strict
  Implicit]; concrete facts are discharged by [lazy] exactly once per Example.
*)

From Coq Require Import NArith List Bool Arith.
From MultisigFormal Require Import
  ElementsJets SimplicityByteDecoder SimplicityStructuralEval
  ElementsConcreteJets Sha256Core SimplicityCmrSha
  CompiledMultisigByteData CompiledMultisigExampleCore MultisigCertificateCore.

Import ListNotations.

(* ---------- scenario data ---------- *)

Definition to_bytesN (bs : list nat) : list N := map N.of_nat bs.

(* The compiled-in participant keys, straight from the exported certificate. *)
Definition participant1_bytes : list N :=
  to_bytesN (nth 0 (cert_participants compiled_multisig_certificate) []).
Definition participant2_bytes : list N :=
  to_bytesN (nth 1 (cert_participants compiled_multisig_certificate) []).

Definition scenario_current_script_hash : list N := repeat 204%N 32.
Definition scenario_input_hash0 : list N := repeat 170%N 32.
Definition scenario_output_hash0 : list N := repeat 187%N 32.
Definition vote1_leaf : list N := repeat 17%N 32.
Definition vote2_leaf : list N := repeat 34%N 32.
Definition vote1_sig : list N := repeat 49%N 64.
Definition vote2_sig : list N := repeat 50%N 64.

(* The BIP-341 nothing-up-my-sleeve internal key hard-coded in the SIMF
   source (multisig_n_of_3.simf). *)
Definition bip341_internal_key : list N :=
  [80;146;155;116;193;160;73;84;183;139;75;96;53;233;122;94;
   7;138;90;15;40;236;150;213;71;191;238;154;206;128;58;192]%N.

(* The vote taproot script hash, mirroring verify_vote_input in the SIMF
   source through the same concrete jet functions the evaluator uses. *)
Definition vote_script_hash (sig leaf : list N) : list N :=
  let state_hash := shadow_finalize (shadow_add shadow_init sig) in
  let state_leaf :=
    shadow_finalize (shadow_add (tagged_ctx tapdata_tag) state_hash) in
  let tap_node := build_tapbranch_bytes leaf state_leaf in
  let tweaked := build_taptweak_bytes bip341_internal_key tap_node in
  shadow_finalize (shadow_add (shadow_add shadow_init [81;32]%N) tweaked).

Definition vote1_script_hash := vote_script_hash vote1_sig vote1_leaf.
Definition vote2_script_hash := vote_script_hash vote2_sig vote2_leaf.

(* Honest environment: input 0 is the multisig input, inputs 1 and 2 are the
   two vote inputs committed through the taproot construction; one proposed
   output. *)
Definition honest_env : ConcreteEnv := {|
  cenv_num_inputs := 3%N;
  cenv_current_index := 0%N;
  cenv_current_script_hash := scenario_current_script_hash;
  cenv_input_script_hashes :=
    [scenario_current_script_hash; vote1_script_hash; vote2_script_hash];
  cenv_input_hashes := [scenario_input_hash0];
  cenv_output_hashes := [scenario_output_hash0]
|}.

(* Vote 2's on-chain commitment is absent (wrong script hash at index 2). *)
Definition uncommitted_vote_env : ConcreteEnv := {|
  cenv_num_inputs := 3%N;
  cenv_current_index := 0%N;
  cenv_current_script_hash := scenario_current_script_hash;
  cenv_input_script_hashes :=
    [scenario_current_script_hash; vote1_script_hash;
     scenario_current_script_hash];
  cenv_input_hashes := [scenario_input_hash0];
  cenv_output_hashes := [scenario_output_hash0]
|}.

(* The proposed output differs from what the participants signed. *)
Definition tampered_outputs_env : ConcreteEnv := {|
  cenv_num_inputs := 3%N;
  cenv_current_index := 0%N;
  cenv_current_script_hash := scenario_current_script_hash;
  cenv_input_script_hashes :=
    [scenario_current_script_hash; vote1_script_hash; vote2_script_hash];
  cenv_input_hashes := [scenario_input_hash0];
  cenv_output_hashes := [repeat 190%N 32]
|}.

(* SHA256(input_hash(0) || output_hash(0)) — the base message of the SIMF
   source for this environment. *)
Definition scenario_base_message : list N :=
  shadow_finalize
    (shadow_add (shadow_add shadow_init scenario_input_hash0)
                scenario_output_hash0).

(* SHA256(vote leaf hash || base message) — the participant message. *)
Definition participant_message_bytes (leaf : list N) : list N :=
  shadow_finalize
    (shadow_add (shadow_add shadow_init leaf) scenario_base_message).

(* The concrete signature_valid: participants 1 and 2 signed their own
   participant messages with their votes' signatures. *)
Definition honest_signature_table : list SigTriple :=
  [(bytes_to_bitsN participant1_bytes,
    bytes_to_bitsN (participant_message_bytes vote1_leaf),
    bytes_to_bitsN vote1_sig);
   (bytes_to_bitsN participant2_bytes,
    bytes_to_bitsN (participant_message_bytes vote2_leaf),
    bytes_to_bitsN vote2_sig)].

Definition single_signature_table : list SigTriple :=
  [(bytes_to_bitsN participant1_bytes,
    bytes_to_bitsN (participant_message_bytes vote1_leaf),
    bytes_to_bitsN vote1_sig)].

(* ---------- witnesses ---------- *)

Definition vote_witness_value (sig leaf : list N) : SValue :=
  VRight (VPair (value_of_bytes 9 sig) (value_of_bytes 8 leaf)).

Definition two_votes_witness : SValue :=
  VPair (vote_witness_value vote1_sig vote1_leaf)
        (VPair (vote_witness_value vote2_sig vote2_leaf) (VLeft VUnit)).

Definition one_vote_witness : SValue :=
  VPair (vote_witness_value vote1_sig vote1_leaf)
        (VPair (VLeft VUnit) (VLeft VUnit)).

Definition total_proposed_outputs_witness : SValue := value_of_N 4 16 1%N.

(* The deployed program's two witness nodes: index 69 carries
   TOTAL_PROPOSED_OUTPUTS (a 16-bit word), index 959 carries VOTES
   (vote x (vote x vote)); both indices and shapes are pinned by the
   exported type table (typed_certificate_types). *)
Definition multisig_witness (votes : SValue) (index : nat) : option SValue :=
  if Nat.eqb index 69 then Some total_proposed_outputs_witness
  else if Nat.eqb index 959 then Some votes
  else None.

(* ---------- running the deployed bytes ---------- *)

Definition multisig_run
    (table : list SigTriple)
    (votes : SValue)
    (env : ConcreteEnv) : EvalResult :=
  match compiled_multisig_streaming_structural_program with
  | Some program =>
      eval_structural_program
        (concrete_jet_sem table env)
        (multisig_witness votes)
        program
        VUnit
  | None => EStuck
  end.

(* ---------- the execution theorems ---------- *)

(* Two committed votes with valid signatures meet the threshold: ACCEPT. *)
Example deployed_multisig_accepts_two_valid_votes :
  multisig_run honest_signature_table two_votes_witness honest_env =
    EValue VUnit.
Proof. lazy. reflexivity. Qed.

(* No valid signature anywhere: REJECT. *)
Example deployed_multisig_rejects_without_valid_signatures :
  multisig_run [] two_votes_witness honest_env = EFail.
Proof. lazy. reflexivity. Qed.

(* One valid vote is below the compiled-in threshold of 2: REJECT. *)
Example deployed_multisig_rejects_below_threshold :
  multisig_run single_signature_table one_vote_witness honest_env = EFail.
Proof. lazy. reflexivity. Qed.

(* A vote whose taproot commitment is not on-chain: REJECT. *)
Example deployed_multisig_rejects_uncommitted_vote :
  multisig_run honest_signature_table two_votes_witness
    uncommitted_vote_env = EFail.
Proof. lazy. reflexivity. Qed.

(* Tampered proposed outputs invalidate every signature's message: REJECT. *)
Example deployed_multisig_rejects_tampered_outputs :
  multisig_run honest_signature_table two_votes_witness
    tampered_outputs_env = EFail.
Proof. lazy. reflexivity. Qed.

(* Packaged behavioral evidence: the deployed artifact's acceptance is
   signature-gated, threshold-gated, commitment-gated and message-gated on
   these scenarios, and no run reaches the structural-error state. *)
Theorem deployed_multisig_execution_behavior :
  multisig_run honest_signature_table two_votes_witness honest_env =
    EValue VUnit /\
  multisig_run [] two_votes_witness honest_env = EFail /\
  multisig_run single_signature_table one_vote_witness honest_env = EFail /\
  multisig_run honest_signature_table two_votes_witness
    uncommitted_vote_env = EFail /\
  multisig_run honest_signature_table two_votes_witness
    tampered_outputs_env = EFail.
Proof.
  split.
  { exact deployed_multisig_accepts_two_valid_votes. }
  split.
  { exact deployed_multisig_rejects_without_valid_signatures. }
  split.
  { exact deployed_multisig_rejects_below_threshold. }
  split.
  { exact deployed_multisig_rejects_uncommitted_vote. }
  exact deployed_multisig_rejects_tampered_outputs.
Qed.
