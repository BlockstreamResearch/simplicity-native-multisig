From Coq Require Import List Bool Arith Lia.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(*
  Elements jets used by crates/contracts/simf/multisig_n_of_3.simf.

  This is intentionally not the full Elements jet family. It is the proof scope
  for the multisig bridge: the byte decoder rejects any jet outside this list,
  and later semantic bridge lemmas only need specifications for these jets.
*)

Inductive ElementsJet :=
| JAdd32
| JBip0340Verify
| JBuildTapbranch
| JBuildTaptweak
| JCurrentIndex
| JCurrentScriptHash
| JEq1
| JEq16
| JEq256
| JEq32
| JIncrement32
| JInputHash
| JInputScriptHash
| JLe32
| JLeftPadLow16_32
| JLeftPadLow8_32
| JLt32
| JNumInputs
| JOutputHash
| JSha256Ctx8Add2
| JSha256Ctx8Add32
| JSha256Ctx8Add64
| JSha256Ctx8Finalize
| JSha256Ctx8Init
| JTapdataInit
| JVerify.

Definition elements_jet_code (j : ElementsJet) : nat * nat :=
  match j with
  | JAdd32 => (2417, 13)
  | JBip0340Verify => (396, 10)
  | JBuildTapbranch => (11810, 14)
  | JBuildTaptweak => (11811, 14)
  | JCurrentIndex => (901, 10)
  | JCurrentScriptHash => (231172, 18)
  | JEq1 => (218, 10)
  | JEq16 => (7024, 15)
  | JEq256 => (14056, 16)
  | JEq32 => (7025, 15)
  | JIncrement32 => (19569, 16)
  | JInputHash => (366, 9)
  | JInputScriptHash => (462371, 19)
  | JLe32 => (639025, 21)
  | JLeftPadLow16_32 => (229730, 20)
  | JLeftPadLow8_32 => (918916, 22)
  | JLt32 => (639089, 21)
  | JNumInputs => (7216, 13)
  | JOutputHash => (360, 9)
  | JSha256Ctx8Add2 => (684, 11)
  | JSha256Ctx8Add32 => (5490, 14)
  | JSha256Ctx8Add64 => (5491, 14)
  | JSha256Ctx8Finalize => (689, 11)
  | JSha256Ctx8Init => (690, 11)
  | JTapdataInit => (413, 10)
  | JVerify => (0, 3)
  end.

Fixpoint bits_of_nat (width n : nat) : list bool :=
  match width with
  | 0 => []
  | S width' =>
      Nat.odd ((n / Nat.pow 2 width') mod 2) :: bits_of_nat width' n
  end.

Definition elements_jet_bits (j : ElementsJet) : list bool :=
  match j with
  | JAdd32 => [false; true; false; false; true; false; true; true; true; false; false; false; true]
  | JBip0340Verify => [false; true; true; false; false; false; true; true; false; false]
  | JBuildTapbranch => [true; false; true; true; true; false; false; false; true; false; false; false; true; false]
  | JBuildTaptweak => [true; false; true; true; true; false; false; false; true; false; false; false; true; true]
  | JCurrentIndex => [true; true; true; false; false; false; false; true; false; true]
  | JCurrentScriptHash => [true; true; true; false; false; false; false; true; true; true; false; false; false; false; false; true; false; false]
  | JEq1 => [false; false; true; true; false; true; true; false; true; false]
  | JEq16 => [false; false; true; true; false; true; true; false; true; true; true; false; false; false; false]
  | JEq256 => [false; false; true; true; false; true; true; false; true; true; true; false; true; false; false; false]
  | JEq32 => [false; false; true; true; false; true; true; false; true; true; true; false; false; false; true]
  | JIncrement32 => [false; true; false; false; true; true; false; false; false; true; true; true; false; false; false; true]
  | JInputHash => [true; false; true; true; false; true; true; true; false]
  | JInputScriptHash => [true; true; true; false; false; false; false; true; true; true; false; false; false; true; false; false; false; true; true]
  | JLe32 => [false; true; false; false; true; true; true; false; false; false; false; false; false; false; false; true; true; false; false; false; true]
  | JLeftPadLow16_32 => [false; false; true; true; true; false; false; false; false; false; false; true; false; true; true; false; false; false; true; false]
  | JLeftPadLow8_32 => [false; false; true; true; true; false; false; false; false; false; false; true; false; true; true; false; false; false; false; true; false; false]
  | JLt32 => [false; true; false; false; true; true; true; false; false; false; false; false; false; false; true; true; true; false; false; false; true]
  | JNumInputs => [true; true; true; false; false; false; false; true; true; false; false; false; false]
  | JOutputHash => [true; false; true; true; false; true; false; false; false]
  | JSha256Ctx8Add2 => [false; true; false; true; false; true; false; true; true; false; false]
  | JSha256Ctx8Add32 => [false; true; false; true; false; true; false; true; true; true; false; false; true; false]
  | JSha256Ctx8Add64 => [false; true; false; true; false; true; false; true; true; true; false; false; true; true]
  | JSha256Ctx8Finalize => [false; true; false; true; false; true; true; false; false; false; true]
  | JSha256Ctx8Init => [false; true; false; true; false; true; true; false; false; true; false]
  | JTapdataInit => [false; true; true; false; false; true; true; true; false; true]
  | JVerify => [false; false; false]
  end.

Definition bits_of_elements_jet := elements_jet_bits.

Fixpoint strip_prefix (prefix bits : list bool) : option (list bool) :=
  match prefix, bits with
  | [], _ => Some bits
  | p :: prefix', b :: bits' =>
      if Bool.eqb p b then strip_prefix prefix' bits' else None
  | _ :: _, [] => None
  end.

Definition multisig_elements_jets : list ElementsJet :=
  [ JAdd32
  ; JBip0340Verify
  ; JBuildTapbranch
  ; JBuildTaptweak
  ; JCurrentIndex
  ; JCurrentScriptHash
  ; JEq1
  ; JEq16
  ; JEq256
  ; JEq32
  ; JIncrement32
  ; JInputHash
  ; JInputScriptHash
  ; JLe32
  ; JLeftPadLow16_32
  ; JLeftPadLow8_32
  ; JLt32
  ; JNumInputs
  ; JOutputHash
  ; JSha256Ctx8Add2
  ; JSha256Ctx8Add32
  ; JSha256Ctx8Add64
  ; JSha256Ctx8Finalize
  ; JSha256Ctx8Init
  ; JTapdataInit
  ; JVerify
  ].

Definition multisig_elements_jet (j : ElementsJet) : Prop :=
  In j multisig_elements_jets.

Theorem elements_jet_is_multisig_elements_jet :
  forall j,
    multisig_elements_jet j.
Proof.
  destruct j; unfold multisig_elements_jet, multisig_elements_jets; simpl;
    tauto.
Qed.

Fixpoint try_decode_elements_jet
    (candidates : list ElementsJet)
    (bits : list bool) : option (ElementsJet * list bool) :=
  match candidates with
  | [] => None
  | candidate :: rest =>
      match strip_prefix (bits_of_elements_jet candidate) bits with
      | Some bits' => Some (candidate, bits')
      | None => try_decode_elements_jet rest bits
      end
  end.

Definition decode_elements_jet (bits : list bool) :
    option (ElementsJet * list bool) :=
  try_decode_elements_jet multisig_elements_jets bits.

Theorem decode_elements_jet_roundtrip :
  forall j rest,
    decode_elements_jet (bits_of_elements_jet j ++ rest) =
      Some (j, rest).
Proof.
  destruct j; reflexivity.
Qed.

Section SemanticInterface.

Variable Hash : Type.
Variable Pubkey : Type.
Variable Signature : Type.
Variable Ctx8 : Type.
Variable Word256 : Type.

Definition U1 := bool.
Definition U8 := nat.
Definition U16 := nat.
Definition U32 := nat.
Definition U256 := Word256.

Record ElementsEnv := {
  env_current_index : U32;
  env_num_inputs : U32;
  env_current_script_hash : U256;
  env_input_script_hash : U32 -> option U256;
  env_input_hash : U32 -> option U256;
  env_output_hash : U32 -> option U256
}.

Record ElementsJetSemantics := {
  sem_add_32 : U32 -> U32 -> bool * U32;
  sem_increment_32 : U32 -> bool * U32;
  sem_eq_1 : U1 -> U1 -> bool;
  sem_eq_16 : U16 -> U16 -> bool;
  sem_eq_32 : U32 -> U32 -> bool;
  sem_eq_256 : U256 -> U256 -> bool;
  sem_le_32 : U32 -> U32 -> bool;
  sem_lt_32 : U32 -> U32 -> bool;
  sem_left_pad_low_8_32 : U8 -> U32;
  sem_left_pad_low_16_32 : U16 -> U32;
  sem_current_index : ElementsEnv -> U32;
  sem_num_inputs : ElementsEnv -> U32;
  sem_current_script_hash : ElementsEnv -> U256;
  sem_input_script_hash : ElementsEnv -> U32 -> option U256;
  sem_input_hash : ElementsEnv -> U32 -> option U256;
  sem_output_hash : ElementsEnv -> U32 -> option U256;
  sem_sha_256_ctx_8_init : Ctx8;
  sem_tapdata_init : Ctx8;
  sem_sha_256_ctx_8_add_2 : Ctx8 -> U16 -> Ctx8;
  sem_sha_256_ctx_8_add_32 : Ctx8 -> U256 -> Ctx8;
  sem_sha_256_ctx_8_add_64 : Ctx8 -> Signature -> Ctx8;
  sem_sha_256_ctx_8_finalize : Ctx8 -> U256;
  sem_build_tapbranch : U256 -> U256 -> U256;
  sem_build_taptweak : U256 -> U256 -> U256;
  sem_bip_0340_verify : Pubkey -> U256 -> Signature -> Prop;
  sem_verify : bool -> Prop;
  sem_word256_as_hash : U256 -> Hash;
  sem_word256_as_pubkey : U256 -> Pubkey
}.

End SemanticInterface.
