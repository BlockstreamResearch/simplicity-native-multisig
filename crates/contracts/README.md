# Contracts

Core Simplicity contracts for the native multisig product live here.

This crate is the source of truth for contract programs, typed parameters, transaction helpers, and contract-level tests.

## Simplex

Contract sources live in `simf/`. Generated Rust artifacts are written to `src/artifacts/` by Simplex and are ignored by git.

```bash
simplex build
```