From Coq Require Import List.
From MultisigFormal Require Import
  CompiledMultisigByteData MultisigTypedCertificate
  CompiledMultisigTypedExampleTypeDefs
  CompiledMultisigTypedExampleArrowDefs1
  CompiledMultisigTypedExampleArrowDefs2
  CompiledMultisigTypedExampleArrowDefs3
  CompiledMultisigTypedExampleTypeTable1
  CompiledMultisigTypedExampleTypeTable2
  CompiledMultisigTypedExampleTypeTable3
  CompiledMultisigTypedExampleTypeTable4.

Import ListNotations.

Definition compiled_multisig_compact_bridge_arrow_defs : list (nat * nat) :=
  compiled_multisig_compact_bridge_arrow_defs_1 ++
  compiled_multisig_compact_bridge_arrow_defs_2 ++
  compiled_multisig_compact_bridge_arrow_defs_3.

Definition compiled_multisig_compact_type_table_entries : list (option nat) :=
  compiled_multisig_compact_type_table_entries_1 ++
  compiled_multisig_compact_type_table_entries_2 ++
  compiled_multisig_compact_type_table_entries_3 ++
  compiled_multisig_compact_type_table_entries_4.

Definition compiled_multisig_compact_typed_certificate :
    CompactCompiledMultisigTypedByteCertificate := {|
  compact_typed_certificate_bytes := compiled_multisig_certificate;
  compact_bridge_type_defs := compiled_multisig_compact_bridge_type_defs;
  compact_bridge_arrow_defs := compiled_multisig_compact_bridge_arrow_defs;
  compact_type_table_entries := compiled_multisig_compact_type_table_entries;
  compact_root_arrow_index := 0
|}.
