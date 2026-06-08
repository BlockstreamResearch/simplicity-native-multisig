use simplicity_native_multisig_contracts::setup_version;

#[test]
fn contracts_crate_is_wired() {
    assert_eq!(setup_version(), "0.1.0");
}
