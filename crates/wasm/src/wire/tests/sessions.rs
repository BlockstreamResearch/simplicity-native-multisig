#![allow(clippy::wildcard_imports)]

use super::super::*;
use super::fixtures::*;

#[test]
fn creates_and_inspects_multisig_descriptor() -> anyhow::Result<()> {
    let keys = participant_keys(repeated_mnemonics())?;
    let descriptor = create_multisig_descriptor(2, &serde_json::to_string(&keys)?)?;
    let inspected = inspect_multisig_descriptor(&descriptor)?;

    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&descriptor)?,
        serde_json::from_str::<serde_json::Value>(&inspected)?
    );

    Ok(())
}
