use std::fmt::Write as _;

use super::CompiledMultisigCertificate;
use super::coq_typed_text::{
    write_coq_typed_bridge_evidence, write_coq_typed_certificate_definition,
    write_coq_typed_decode_evidence, write_coq_typed_program_definitions,
    write_coq_typed_translation_theorems,
};
use super::coq_types::coq_type_artifact;

const ARROW_CHUNK_ENTRIES: usize = 330;
const TYPE_TABLE_CHUNK_ENTRIES: usize = 340;

/// A generated Coq source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoqModuleFile {
    /// Filename relative to the target Coq project directory.
    pub filename: String,
    /// Coq source text for the file.
    pub contents: String,
}

impl CompiledMultisigCertificate {
    /// Split Coq modules for the byte certificate and compact typed artifact.
    ///
    /// The split layout matches the checked formal modules and keeps generated
    /// data files small enough to review directly.
    #[must_use]
    pub fn coq_typed_certificate_modules(&self) -> Vec<CoqModuleFile> {
        let artifact = coq_type_artifact(self);
        let mut modules = vec![CoqModuleFile {
            filename: String::from("CompiledMultisigExample.v"),
            contents: self.coq_certificate_module(),
        }];

        modules.push(coq_list_module(
            "CompiledMultisigTypedExampleTypeDefs.v",
            Some("MultisigTypedCertificate"),
            "compiled_multisig_compact_bridge_type_defs",
            "list CompactBridgeTypeDef",
            &artifact.type_definitions,
        ));

        let arrow_modules = chunked_modules(
            "CompiledMultisigTypedExampleArrowDefs",
            "compiled_multisig_compact_bridge_arrow_defs",
            "list (nat * nat)",
            ARROW_CHUNK_ENTRIES,
            &artifact.arrow_definitions,
        );
        let type_table_modules = chunked_modules(
            "CompiledMultisigTypedExampleTypeTable",
            "compiled_multisig_compact_type_table_entries",
            "list (option nat)",
            TYPE_TABLE_CHUNK_ENTRIES,
            &artifact.type_table_entries,
        );

        let arrow_names = definition_names(
            "compiled_multisig_compact_bridge_arrow_defs",
            arrow_modules.len(),
        );
        let type_table_names = definition_names(
            "compiled_multisig_compact_type_table_entries",
            type_table_modules.len(),
        );

        modules.extend(arrow_modules);
        modules.extend(type_table_modules);

        let mut data_module = String::new();
        data_module.push_str("From Coq Require Import List.\n");
        data_module.push_str("From MultisigFormal Require Import\n");
        data_module.push_str(
            "  CompiledMultisigExample MultisigTypedCertificate CompiledMultisigTypedExampleTypeDefs",
        );

        for number in 1..=arrow_names.len() {
            write!(
                data_module,
                " CompiledMultisigTypedExampleArrowDefs{number}"
            )
            .expect("writing to a String cannot fail");
        }
        for number in 1..=type_table_names.len() {
            write!(
                data_module,
                " CompiledMultisigTypedExampleTypeTable{number}"
            )
            .expect("writing to a String cannot fail");
        }

        data_module.push_str(".\n\nImport ListNotations.\n\n");
        write_concat_definition(
            &mut data_module,
            "compiled_multisig_compact_bridge_arrow_defs",
            "list (nat * nat)",
            &arrow_names,
        );
        write_concat_definition(
            &mut data_module,
            "compiled_multisig_compact_type_table_entries",
            "list (option nat)",
            &type_table_names,
        );
        writeln!(
            data_module,
            "Definition compiled_multisig_compact_typed_certificate :\n    CompactCompiledMultisigTypedByteCertificate := {{|"
        )
        .expect("writing to a String cannot fail");
        data_module
            .push_str("  compact_typed_certificate_bytes := compiled_multisig_certificate;\n");
        data_module.push_str(
            "  compact_bridge_type_defs := compiled_multisig_compact_bridge_type_defs;\n",
        );
        data_module.push_str(
            "  compact_bridge_arrow_defs := compiled_multisig_compact_bridge_arrow_defs;\n",
        );
        data_module.push_str(
            "  compact_type_table_entries := compiled_multisig_compact_type_table_entries;\n",
        );
        writeln!(
            data_module,
            "  compact_root_arrow_index := {}",
            artifact.root_arrow
        )
        .expect("writing to a String cannot fail");
        data_module.push_str("|}.\n");

        modules.push(CoqModuleFile {
            filename: String::from("CompiledMultisigTypedExampleData.v"),
            contents: data_module,
        });

        let mut wrapper = String::new();
        wrapper.push_str("From Coq Require Import List.\n");
        wrapper.push_str("From MultisigFormal Require Export CompiledMultisigTypedExampleData.\n");
        wrapper.push_str("From MultisigFormal Require Import\n");
        wrapper
            .push_str("  BridgeTypeTranslation CmrWellFormed SimplicityByteDecoder TypedBridge\n");
        wrapper.push_str(
            "  MultisigCertificate MultisigTypedCertificate CompiledMultisigExample.\n\n",
        );
        wrapper.push_str("Import ListNotations.\n\n");
        write_coq_typed_certificate_definition(&mut wrapper);
        write_coq_typed_translation_theorems(&mut wrapper);
        write_coq_typed_program_definitions(&mut wrapper);
        write_coq_typed_decode_evidence(&mut wrapper);
        write_coq_typed_bridge_evidence(&mut wrapper);

        modules.push(CoqModuleFile {
            filename: String::from("CompiledMultisigTypedExample.v"),
            contents: wrapper,
        });

        modules
    }
}

fn chunked_modules(
    file_prefix: &str,
    definition_prefix: &str,
    typ: &str,
    chunk_size: usize,
    entries: &[String],
) -> Vec<CoqModuleFile> {
    entries
        .chunks(chunk_size)
        .enumerate()
        .map(|(index, chunk)| {
            let number = index + 1;
            coq_list_module(
                &format!("{file_prefix}{number}.v"),
                None,
                &format!("{definition_prefix}_{number}"),
                typ,
                chunk,
            )
        })
        .collect()
}

fn coq_list_module(
    filename: &str,
    multisig_imports: Option<&str>,
    definition_name: &str,
    typ: &str,
    entries: &[String],
) -> CoqModuleFile {
    let mut contents = String::from("From Coq Require Import List.\n");
    if let Some(imports) = multisig_imports {
        writeln!(contents, "From MultisigFormal Require Import {imports}.")
            .expect("writing to a String cannot fail");
    }
    contents.push_str("\nImport ListNotations.\n\n");
    writeln!(contents, "Definition {definition_name} : {typ} := [")
        .expect("writing to a String cannot fail");
    for (index, entry) in entries.iter().enumerate() {
        let terminator = if index + 1 == entries.len() { "" } else { ";" };
        writeln!(contents, "  {entry}{terminator}").expect("writing to a String cannot fail");
    }
    contents.push_str("].\n");

    CoqModuleFile {
        filename: String::from(filename),
        contents,
    }
}

fn write_concat_definition(module: &mut String, name: &str, typ: &str, chunks: &[String]) {
    writeln!(module, "Definition {name} : {typ} :=").expect("writing to a String cannot fail");
    for (index, chunk) in chunks.iter().enumerate() {
        let terminator = if index + 1 == chunks.len() {
            "."
        } else {
            " ++"
        };
        writeln!(module, "  {chunk}{terminator}").expect("writing to a String cannot fail");
    }
    module.push('\n');
}

fn definition_names(prefix: &str, count: usize) -> Vec<String> {
    (1..=count)
        .map(|number| format!("{prefix}_{number}"))
        .collect()
}
