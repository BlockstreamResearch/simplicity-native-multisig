# Simplicity Native Multisig

## Repository layout

- `crates/contracts` - core Simplicity contracts and Rust contract helpers.
- `crates/uniffi` - native bindings surface for mobile and desktop consumers.
- `crates/wasm` - WebAssembly bindings surface for browser and JavaScript consumers.
- `web` - web interface.

## Tooling

This workspace uses Rust 2024 and Simplex `v0.0.5`.

Install Simplex:

```bash
curl -fsSL https://smplx.simplicity-lang.org | bash
simplexup --install v0.0.5
simplexup --use v0.0.5
```

Generate contract artifacts before full workspace checks:

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
simplex test --nocapture
```
