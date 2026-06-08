//! WASM bindings for Simplicity Native Multisig.

use wasm_bindgen::prelude::*;

/// Returns the core contracts setup version.
#[wasm_bindgen(js_name = setupVersion)]
#[must_use]
pub fn setup_version() -> String {
    contracts::setup_version().to_owned()
}

#[cfg(test)]
mod tests {
    use super::setup_version;

    #[test]
    fn exposes_contract_setup_version() {
        assert_eq!(setup_version(), "0.1.0");
    }
}
