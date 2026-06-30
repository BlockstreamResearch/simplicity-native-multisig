use std::path::Path;

use simplicity_native_multisig_contracts::multisig::{MultisigBuilder, PARTICIPANT_COUNT};
use simplicityhl::elements::schnorr::XOnlyPublicKey;

fn main() -> anyhow::Result<()> {
    let args = std::env::args().collect::<Vec<_>>();
    let program_name = args
        .first()
        .map_or("export_multisig_certificate", String::as_str);

    if args.len() == 2 && matches!(args[1].as_str(), "-h" | "--help") {
        println!("{}", usage(program_name));
        return Ok(());
    }

    let format = args[1].as_str();
    let writes_split_modules = format == "coq-typed-split";
    let expected_len = if writes_split_modules {
        3 + 1 + PARTICIPANT_COUNT
    } else {
        2 + 1 + PARTICIPANT_COUNT
    };

    if args.len() != expected_len {
        anyhow::bail!("{}", usage(program_name));
    }

    let threshold_index = if writes_split_modules { 3 } else { 2 };
    let threshold = args[threshold_index].parse::<u32>().map_err(|error| {
        anyhow::anyhow!("invalid threshold '{}': {error}", args[threshold_index])
    })?;
    let participants = [
        parse_x_only_public_key("participant1", &args[threshold_index + 1])?,
        parse_x_only_public_key("participant2", &args[threshold_index + 2])?,
        parse_x_only_public_key("participant3", &args[threshold_index + 3])?,
    ];

    let certificate = MultisigBuilder::new(threshold, participants)?.compiled_certificate()?;

    match format {
        "json" => println!("{}", serde_json::to_string_pretty(&certificate.artifact())?),
        "coq" => print!("{}", certificate.coq_certificate_module()),
        "coq-typed" => print!("{}", certificate.coq_typed_certificate_module()),
        "coq-typed-split" => {
            let output_dir = Path::new(&args[2]);
            std::fs::create_dir_all(output_dir)?;
            for module in certificate.coq_typed_certificate_modules() {
                std::fs::write(output_dir.join(module.filename), module.contents)?;
            }
        }
        _ => anyhow::bail!("unknown format '{format}'\n\n{}", usage(program_name)),
    }

    Ok(())
}

fn parse_x_only_public_key(label: &str, value: &str) -> anyhow::Result<XOnlyPublicKey> {
    let bytes = hex::decode(value.trim())
        .map_err(|error| anyhow::anyhow!("{label} must be hex encoded: {error}"))?;

    if bytes.len() != 32 {
        anyhow::bail!("{label} must be 32 bytes, got {}", bytes.len());
    }

    XOnlyPublicKey::from_slice(&bytes)
        .map_err(|error| anyhow::anyhow!("{label} is not a valid x-only public key: {error}"))
}

fn usage(program_name: &str) -> String {
    format!(
        "usage: {program_name} <json|coq|coq-typed> <threshold> <participant1_xonly_hex> <participant2_xonly_hex> <participant3_xonly_hex>\n       {program_name} coq-typed-split <output_dir> <threshold> <participant1_xonly_hex> <participant2_xonly_hex> <participant3_xonly_hex>"
    )
}
