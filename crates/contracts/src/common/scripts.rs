use simplicityhl::elements::hashes::{Hash, sha256};
use simplicityhl::elements::script::Instruction;
use simplicityhl::elements::taproot::LeafVersion;
use simplicityhl::elements::{Script, Transaction, TxIn, opcodes};
use simplicityhl::simplicity::Cmr;

/// Hash a script exactly as `jet::input_script_hash` exposes it.
#[must_use]
pub fn script_hash(script: &Script) -> sha256::Hash {
    sha256::Hash::hash(script.as_bytes())
}

/// Iterate over the contiguous transaction input prefix locked by `multisig_script`.
///
/// The returned input references are borrowed from `transaction`.
pub fn multisig_input_prefix<'tx>(
    transaction: &'tx Transaction,
    multisig_script: &Script,
) -> impl Iterator<Item = &'tx TxIn> + 'tx {
    let current_script_hash = script_hash(multisig_script);

    transaction
        .input
        .iter()
        .take_while(move |input| script_hash(&input.script_sig) == current_script_hash)
}

pub fn script_ver(cmr: Cmr) -> (Script, LeafVersion) {
    (
        Script::from(cmr.as_ref().to_vec()),
        simplicityhl::simplicity::leaf_version(),
    )
}

/// Return the single payload from a standard `OP_RETURN` output script.
///
/// The boolean is true when the script has pushes after the first payload.
#[must_use]
pub fn op_return_payload(script: &Script) -> Option<(&[u8], bool)> {
    let mut instructions = script.instructions();

    match instructions.next() {
        Some(Ok(Instruction::Op(op))) if op == opcodes::all::OP_RETURN => {}
        Some(Ok(_) | Err(_)) | None => return None,
    }

    let Some(Ok(Instruction::PushBytes(payload))) = instructions.next() else {
        return None;
    };

    Some((payload, instructions.next().is_some()))
}
