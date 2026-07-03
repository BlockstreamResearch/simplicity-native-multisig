# Simplicity Native Multisig

## Repository layout

- `crates/contracts` - core Simplicity contracts and Rust contract helpers.
- `crates/wasm` - WebAssembly bindings surface for browser and JavaScript consumers.
- `web` - web interface.
- `formal` - Rocq formal verification of the multisig contracts: axiom-free,
  kernel-checked proofs from the abstract security model down to the deployed
  compiled bytes (decode, type check, byte-exact CMR via self-contained
  SHA-256, and in-Coq execution of the deployed program). See
  `formal/README.md` for the claims and their trust boundaries.
- `permissionless-simplicity-multisig` - paper: Permissionless Multisig using Simplicity.
- `programmable-signature-tex` - original paper draft: Programmable Signatures with Simplicity.

## Tooling

This workspace uses Rust 2024 and Simplex `v0.0.6`.

Install Simplex:

```bash
curl -fsSL https://smplx.simplicity-lang.org | bash
simplexup --install v0.0.6
simplexup --use v0.0.6
```

Generate ignored contract artifacts for inspection under `target/simplex-artifacts/contracts`:

```bash
cd crates/contracts
simplex build
```

Run local checks from the repository root:

```bash
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
```

Run Simplex contract tests from `crates/contracts`:

```bash
simplex test
```
