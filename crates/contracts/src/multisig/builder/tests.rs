use super::coq::coq_byte_list;
use super::*;

use simplicityhl::elements::schnorr::Keypair;
use simplicityhl::elements::secp256k1_zkp::{SECP256K1, SecretKey};
use simplicityhl::simplicity::jet::Elements;
use simplicityhl::simplicity::{BitIter, CommitNode};

fn test_participants() -> anyhow::Result<[XOnlyPublicKey; PARTICIPANT_COUNT]> {
    let keypair = |byte| -> anyhow::Result<Keypair> {
        let secret_key = SecretKey::from_slice(&[byte; 32])?;
        Ok(Keypair::from_secret_key(SECP256K1, &secret_key))
    };

    Ok([
        keypair(1)?.x_only_public_key().0,
        keypair(2)?.x_only_public_key().0,
        keypair(3)?.x_only_public_key().0,
    ])
}

#[test]
fn rejects_duplicate_participants() -> anyhow::Result<()> {
    let mut participants = test_participants()?;
    participants[2] = participants[0];

    let error = MultisigBuilder::new(2, participants).unwrap_err();

    assert_eq!(error.to_string(), "participants must be distinct");

    Ok(())
}

#[test]
fn rejects_threshold_outside_participant_count() -> anyhow::Result<()> {
    let participants = test_participants()?;

    let zero_error = MultisigBuilder::new(0, participants).unwrap_err();
    let too_large_error = MultisigBuilder::new(4, participants).unwrap_err();

    assert_eq!(zero_error.to_string(), "invalid threshold value: 0");
    assert_eq!(too_large_error.to_string(), "invalid threshold value: 4");

    Ok(())
}

#[test]
fn compiled_certificate_round_trips_through_commit_decoder() -> anyhow::Result<()> {
    let builder = MultisigBuilder::new(2, test_participants()?)?;
    let certificate = builder.compiled_certificate()?;

    assert_eq!(certificate.cmr, builder.cmr()?);
    assert_eq!(certificate.cmr.as_ref().len(), 32);
    assert!(!certificate.program_bytes.is_empty());

    let artifact = certificate.artifact();
    assert_eq!(artifact.threshold, builder.parameters.threshold());
    assert_eq!(artifact.cmr_hex.len(), 64);
    assert_eq!(
        artifact.program_hex.len(),
        certificate.program_bytes.len() * 2
    );
    assert_eq!(
        artifact.participants_hex,
        builder
            .parameters
            .participants()
            .map(|participant| hex::encode(participant.serialize()))
    );

    let artifact_json: serde_json::Value = serde_json::to_value(&artifact)?;
    assert_eq!(
        artifact_json["cmr_hex"].as_str(),
        Some(artifact.cmr_hex.as_str())
    );
    assert_eq!(
        artifact_json["program_hex"].as_str(),
        Some(artifact.program_hex.as_str())
    );

    let decoded = CommitNode::<Elements>::decode(BitIter::from(certificate.program_bytes.clone()))
        .map_err(|error| anyhow::anyhow!("{error}"))?;

    assert_eq!(decoded.cmr(), certificate.cmr);
    assert_eq!(decoded.to_vec_without_witness(), certificate.program_bytes);
    assert_eq!(certificate.type_table, encoded_type_table(&decoded));
    assert_eq!(&certificate.root_arrow, decoded.arrow());
    assert!(!certificate.type_table.is_empty());

    Ok(())
}

#[test]
fn compiled_certificate_exports_coq_module() -> anyhow::Result<()> {
    let builder = MultisigBuilder::new(2, test_participants()?)?;
    let certificate = builder.compiled_certificate()?;
    let coq_module = certificate.coq_certificate_module();

    assert!(coq_module.contains("From Coq Require Import List."));
    assert!(
        coq_module.contains(
            "From MultisigFormal Require Import\n  SimplicityByteDecoder MultisigCertificate MultisigSourceBlocks."
        )
    );
    assert!(coq_module.contains(
        "Definition compiled_multisig_certificate : CompiledMultisigByteCertificate := {|"
    ));
    assert!(coq_module.contains("  cert_threshold := 2;"));
    assert!(coq_module.contains(&format!(
        "  cert_program_bytes := {};",
        coq_byte_list(certificate.program_bytes.iter().copied())
    )));
    assert!(coq_module.contains(&format!(
        "  cert_cmr_bytes := {}",
        coq_byte_list(certificate.cmr.as_ref().iter().copied())
    )));
    assert!(!coq_module.contains("Definition compiled_multisig_type_table"));
    assert!(!coq_module.contains("compiled_multisig_typed_certificate"));
    assert!(
        coq_module
            .contains("Definition compiled_multisig_decoded_program : option StructuralProgram :=")
    );
    assert!(coq_module.contains("  check_compiled_multisig_byte_certificate_without_cmr"));
    assert!(coq_module.contains("    compiled_multisig_certificate."));
    assert!(coq_module.contains(
        "Definition compiled_multisig_streaming_decoded_program : option StructuralProgram :="
    ));
    assert!(
        coq_module.contains("  check_compiled_multisig_byte_certificate_streaming_without_cmr")
    );
    assert!(coq_module.contains("Definition compiled_multisig_streaming_checked_program"));
    assert!(coq_module.contains("  check_compiled_multisig_byte_certificate_streaming"));
    assert!(!coq_module.contains("compiled_multisig_streaming_typed_checked_program"));
    assert!(coq_module.contains("Definition compiled_multisig_streaming_raw_program :="));
    assert!(coq_module.contains("  decode_program_bytes_streaming"));
    assert!(coq_module.contains("Example compiled_multisig_streaming_raw_program_is_some :"));
    assert!(coq_module.contains("  lazy."));
    assert!(coq_module.contains("Definition compiled_multisig_streaming_structural_program :="));
    assert!(coq_module.contains("  decode_structural_program_bytes_streaming"));
    assert!(
        coq_module.contains("Example compiled_multisig_streaming_structural_program_is_some :")
    );
    assert!(coq_module.contains("Theorem compiled_multisig_streaming_structural_program_exists :"));
    assert!(coq_module.contains("Example compiled_multisig_streaming_decoded_program_is_some :"));
    assert!(coq_module.contains("Theorem compiled_multisig_streaming_decode_evidence :"));
    assert!(coq_module.contains("    CompiledMultisigByteCertificateStreamingDecodeEvidence"));
    assert!(coq_module.contains("Theorem compiled_multisig_streaming_source_static_fields :"));
    assert!(coq_module.contains("Theorem compiled_multisig_certificate_source_static_fields :"));
    assert!(
        coq_module.contains("Theorem compiled_multisig_streaming_bridge_evidence_if_checked_cmr :")
    );
    assert!(coq_module.contains("    CompiledMultisigByteCertificateStreamingBridgeEvidence"));
    assert!(coq_module.contains("Theorem compiled_multisig_decode_evidence_if_some :"));
    assert!(coq_module.contains("    CompiledMultisigByteCertificateDecodeEvidence"));

    for participant in builder.parameters.participants() {
        assert!(coq_module.contains(&coq_byte_list(participant.serialize())));
    }

    Ok(())
}

#[test]
fn compiled_certificate_exports_typed_coq_module() -> anyhow::Result<()> {
    let builder = MultisigBuilder::new(2, test_participants()?)?;
    let certificate = builder.compiled_certificate()?;
    let coq_module = certificate.coq_typed_certificate_module();

    assert!(coq_module.contains(
        "From MultisigFormal Require Import\n  BridgeTypeTranslation CmrWellFormed SimplicityByteDecoder TypedBridge\n  MultisigCertificate MultisigTypedCertificate MultisigSourceBlocks."
    ));
    assert!(coq_module.contains(
        "Definition compiled_multisig_compact_typed_certificate : CompactCompiledMultisigTypedByteCertificate := {|"
    ));
    assert!(!coq_module.contains("Definition compiled_bridge_ty_0 : BridgeType :="));
    assert!(!coq_module.contains("Definition compiled_bridge_arrow_0 : BridgeArrow :="));
    assert!(coq_module.contains("  compact_bridge_type_defs := ["));
    assert!(coq_module.contains("    CBTDUnit"));
    assert!(coq_module.contains("    CBTDProd "));
    assert!(coq_module.contains("  compact_bridge_arrow_defs := ["));
    assert!(coq_module.contains("    (0, 0)"));
    assert!(coq_module.contains("  compact_type_table_entries := ["));
    assert!(coq_module.contains("    Some "));
    let table_start = coq_module
        .find("  compact_type_table_entries := [")
        .expect("compact type table entries marker should exist");
    let table_after_start = &coq_module[table_start..];
    let table_end = table_after_start
        .find("  ];")
        .expect("compact type table entries terminator should exist");
    let table_body = &table_after_start[..table_end];
    assert_eq!(
        table_body.matches("    Some ").count(),
        certificate
            .type_table
            .iter()
            .filter(|entry| entry.is_some())
            .count()
    );
    assert_eq!(
        table_body.matches("    None").count(),
        certificate
            .type_table
            .iter()
            .filter(|entry| entry.is_none())
            .count()
    );
    assert!(coq_module.contains("  compact_root_arrow_index := "));
    assert!(coq_module.contains(
        "Definition compiled_multisig_typed_certificate : option CompiledMultisigTypedByteCertificate :="
    ));
    assert!(coq_module.contains(
        "  expand_compact_typed_certificate compiled_multisig_compact_typed_certificate."
    ));
    assert!(coq_module.contains("Example compiled_multisig_compact_type_defs_atom_free :"));
    assert!(coq_module.contains("Theorem compiled_multisig_typed_certificate_atom_free :"));
    assert!(
        coq_module.contains(
            "Theorem compiled_multisig_typed_certificate_translates_to_core_type_algebra :"
        )
    );
    assert!(coq_module.contains("Definition compiled_multisig_streaming_typed_checked_program"));
    assert!(coq_module.contains("Definition compiled_multisig_streaming_typed_decoded_program"));
    assert!(
        coq_module.contains("Example compiled_multisig_streaming_typed_decoded_program_is_some :")
    );
    assert!(coq_module.contains("Definition compiled_multisig_type_check_for_program"));
    assert!(coq_module.contains(
        "  check_compiled_multisig_compact_typed_byte_certificate_streaming_without_cmr"
    ));
    assert!(coq_module.contains("Theorem compiled_multisig_streaming_typed_decode_evidence :"));
    assert!(
        coq_module
            .contains("Theorem compiled_multisig_streaming_typed_decode_evidence_if_checked :")
    );
    assert!(
        coq_module
            .contains("    CompactTypedCompiledMultisigByteCertificateStreamingDecodeEvidence")
    );
    assert!(coq_module.contains(
        "Theorem compiled_multisig_streaming_typed_bridge_evidence_from_cmr_if_checked :"
    ));
    assert!(coq_module.contains(
        "Theorem compiled_multisig_streaming_typed_decode_evidence_from_byte_evidence_if_type_checked :"
    ));
    assert!(coq_module.contains("    CompiledMultisigByteCertificateStreamingDecodeEvidence"));
    assert!(coq_module.contains("    compiled_multisig_type_check_for_program program = true ->"));
    assert!(
        coq_module.contains("  check_compiled_multisig_compact_typed_byte_certificate_streaming")
    );
    assert!(
        coq_module
            .contains("Theorem compiled_multisig_streaming_typed_bridge_evidence_if_checked :")
    );
    assert!(
        coq_module
            .contains("    CompactTypedCompiledMultisigByteCertificateStreamingBridgeEvidence")
    );

    Ok(())
}

#[test]
fn compiled_certificate_exports_split_typed_coq_modules() -> anyhow::Result<()> {
    let builder = MultisigBuilder::new(2, test_participants()?)?;
    let certificate = builder.compiled_certificate()?;
    let modules = certificate.coq_typed_certificate_modules();
    let module_names = modules
        .iter()
        .map(|module| module.filename.as_str())
        .collect::<Vec<_>>();

    assert_eq!(module_names.first(), Some(&"CompiledMultisigExample.v"));
    assert!(module_names.contains(&"CompiledMultisigTypedExampleTypeDefs.v"));
    assert!(module_names.contains(&"CompiledMultisigTypedExampleData.v"));
    assert_eq!(module_names.last(), Some(&"CompiledMultisigTypedExample.v"));
    assert!(
        module_names
            .iter()
            .any(|name| name.starts_with("CompiledMultisigTypedExampleArrowDefs"))
    );
    assert!(
        module_names
            .iter()
            .any(|name| name.starts_with("CompiledMultisigTypedExampleTypeTable"))
    );

    for module in &modules {
        assert!(
            module.contents.lines().count() <= 450,
            "{} is too large",
            module.filename
        );
    }

    let byte_module = module_contents(&modules, "CompiledMultisigExample.v");
    assert!(byte_module.contains("Theorem compiled_multisig_certificate_source_static_fields :"));

    let data_module = module_contents(&modules, "CompiledMultisigTypedExampleData.v");
    assert!(
        data_module
            .contains("compact_bridge_type_defs := compiled_multisig_compact_bridge_type_defs;")
    );
    assert!(
        data_module.contains(
            "compact_type_table_entries := compiled_multisig_compact_type_table_entries;"
        )
    );

    let wrapper = module_contents(&modules, "CompiledMultisigTypedExample.v");
    assert!(
        wrapper.contains("From MultisigFormal Require Export CompiledMultisigTypedExampleData.")
    );
    assert!(
        wrapper.contains(
            "Theorem compiled_multisig_typed_certificate_translates_to_core_type_algebra :"
        )
    );
    assert!(wrapper.contains(
        "Theorem compiled_multisig_streaming_typed_checked_byte_bridge_evidence_if_checked :"
    ));

    Ok(())
}

fn module_contents<'a>(modules: &'a [CoqModuleFile], filename: &str) -> &'a str {
    modules
        .iter()
        .find(|module| module.filename == filename)
        .map(|module| module.contents.as_str())
        .expect("generated module should exist")
}
