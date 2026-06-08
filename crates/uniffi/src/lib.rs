//! UniFFI bindings for Simplicity Native Multisig.

/// Returns the core contracts setup version.
#[uniffi::export]
pub fn setup_version() -> String {
    contracts::setup_version().to_owned()
}

uniffi::setup_scaffolding!();

#[cfg(test)]
mod tests {
    use super::setup_version;

    #[test]
    fn exposes_contract_setup_version() {
        assert_eq!(setup_version(), "0.1.0");
    }
}
