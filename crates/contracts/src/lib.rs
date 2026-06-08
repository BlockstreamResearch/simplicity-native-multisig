//! Core Simplicity contracts for native multisig.

pub mod artifacts;

/// Workspace setup version exposed for binding smoke tests.
pub const SETUP_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Returns the current setup version.
#[must_use]
pub const fn setup_version() -> &'static str {
    SETUP_VERSION
}

#[cfg(test)]
mod tests {
    use super::setup_version;

    #[test]
    fn exposes_setup_version() {
        assert_eq!(setup_version(), "0.1.0");
    }
}
