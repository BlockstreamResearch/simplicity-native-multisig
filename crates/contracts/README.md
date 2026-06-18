# Contracts

Core Simplicity contracts for the native multisig product live here.

This crate is the source of truth for contract programs, typed parameters, transaction helpers, and contract-level tests.

## Simplex

Contract sources live in `simf/`. Generated Rust artifacts are written to `src/artifacts/` by Simplex and are ignored by git.

```bash
simplex build
```

The current proof-of-concept contract is `simf/multisig_n_of_3.simf`.
Participants sign a proposal message built from co-spent multisig input hashes, up
to two proposed output hashes, and the vote executable leaf hash.
