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
            "From MultisigFormal Require Import SimplicityByteDecoder MultisigCertificate."
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

    for participant in builder.parameters.participants() {
        assert!(coq_module.contains(&coq_byte_list(participant.serialize())));
    }

    // Data only: proofs are hand-maintained in formal/, never regenerated.
    assert!(!coq_module.contains("Theorem "));
    assert!(!coq_module.contains("Example "));
    assert!(!coq_module.contains("Proof."));

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

    assert_eq!(module_names.first(), Some(&"CompiledMultisigByteData.v"));
    assert!(module_names.contains(&"CompiledMultisigTypedExampleTypeDefs.v"));
    assert_eq!(
        module_names.last(),
        Some(&"CompiledMultisigTypedExampleData.v")
    );
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
        // Data only: no proof text is ever generated.
        assert!(
            !module.contents.contains("Theorem ")
                && !module.contents.contains("Example ")
                && !module.contents.contains("Proof."),
            "{} contains proof text",
            module.filename
        );
    }

    let byte_module = module_contents(&modules, "CompiledMultisigByteData.v");
    assert!(byte_module.contains(
        "Definition compiled_multisig_certificate : CompiledMultisigByteCertificate := {|"
    ));

    let type_defs = module_contents(&modules, "CompiledMultisigTypedExampleTypeDefs.v");
    assert!(type_defs.contains(
        "Definition compiled_multisig_compact_bridge_type_defs : list CompactBridgeTypeDef := ["
    ));
    assert!(type_defs.contains("  CBTDUnit"));

    let data_module = module_contents(&modules, "CompiledMultisigTypedExampleData.v");
    assert!(data_module.contains(
        "From MultisigFormal Require Import\n  CompiledMultisigByteData MultisigTypedCertificate"
    ));
    assert!(
        data_module.contains("compact_typed_certificate_bytes := compiled_multisig_certificate;")
    );
    assert!(
        data_module
            .contains("compact_bridge_type_defs := compiled_multisig_compact_bridge_type_defs;")
    );
    assert!(
        data_module.contains(
            "compact_type_table_entries := compiled_multisig_compact_type_table_entries;"
        )
    );
    assert!(data_module.contains("compact_root_arrow_index := "));

    Ok(())
}

fn module_contents<'a>(modules: &'a [CoqModuleFile], filename: &str) -> &'a str {
    modules
        .iter()
        .find(|module| module.filename == filename)
        .map(|module| module.contents.as_str())
        .expect("generated module should exist")
}
