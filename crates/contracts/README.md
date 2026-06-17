# Contracts

Core Simplicity contracts for the native multisig product live here.

This crate is the source of truth for contract programs, typed parameters, transaction helpers, and contract-level tests.

## Simplex

Contract sources live in `simf/`. Generated Rust artifacts are written to `src/artifacts/` by Simplex and are ignored by git.

```bash
simplex build
```

The current proof-of-concept contract is `simf/native_multisig_poc.simf`.
It models a 2-of-3 covenant multisig where the only contract state is a `nonce`. 
The signed proposal message is `jet::outputs_hash()`, and the state transition checks
that the next covenant output commits to `nonce + 1`.
