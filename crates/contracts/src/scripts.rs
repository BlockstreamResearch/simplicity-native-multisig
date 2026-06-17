use simplex::simplicityhl::elements::Script;
use simplex::simplicityhl::elements::hashes::{Hash, HashEngine, sha256};
use simplex::simplicityhl::elements::taproot::LeafVersion;
use simplex::simplicityhl::simplicity::Cmr;

/// Create a SHA256 context, initialized with a "`TapData`" tag and data
///
/// Based on the C implementation of the `tapdata_init` jet:
/// <https://github.com/BlockstreamResearch/simplicity/blob/d190505509f4c04b1b9193c6739515f9faa18aac/C/jets.c#L1408>
#[must_use]
pub fn tap_data_hash(data: &[u8]) -> sha256::Hash {
    let tag = sha256::Hash::hash(b"TapData");
    let mut eng = sha256::Hash::engine();
    eng.input(tag.as_byte_array());
    eng.input(tag.as_byte_array());
    eng.input(data);
    sha256::Hash::from_engine(eng)
}

pub(crate) fn script_ver(cmr: Cmr) -> (Script, LeafVersion) {
    (
        Script::from(cmr.as_ref().to_vec()),
        simplex::simplicityhl::simplicity::leaf_version(),
    )
}
