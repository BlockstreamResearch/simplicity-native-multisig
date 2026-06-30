# Contracts

Core Simplicity contracts for the native multisig product live here.

This crate is the source of truth for contract programs, typed parameters, transaction helpers, and contract-level tests.

## Simplex

Contract sources live in `simf/`. Generated Rust artifacts are written to
`../../target/simplex-artifacts/contracts/` by Simplex and are ignored by git.
They are useful for inspection, but they are not the public contract API.

```bash
simplex build
```

The current protocol sources are `simf/multisig_n_of_3.simf` and `simf/vote.simf`.
Rust modules keep those files as the source of truth: builders compile and
address covenant instances, descriptors expose indexer-facing script matches,
messages reconstruct participant signing hashes, and the v1 on-chain encoder
publishes proposal hashes through OP_RETURN outputs.

## Formal artifact export

The multisig builder can export the canonical no-witness compiled Simplicity
bytes, the CMR computed from the same committed program, and the static
parameters as JSON, a lean Coq byte-certificate module, or a typed Coq
certificate module:

```bash
cargo run -p simplicity-native-multisig-contracts \
  --example export_multisig_certificate -- \
  coq 2 \
  <participant1_xonly_hex> \
  <participant2_xonly_hex> \
  <participant3_xonly_hex>
```

Use `json` instead of `coq` for the stable machine-readable certificate,
`coq-typed` for a single Coq module that emits a compact indexed per-node type
artifact, or `coq-typed-split <output_dir>` for the same byte and typed
certificate split into the formal tree's smaller
`CompiledMultisigTypedExample*.v` modules. Coq expands that artifact before
running the typed checker, and the generated typed module proves the concrete
compact typed decoder returns `Some program`. That
checker proves the type-table length, real-node/hidden-placeholder entry shape,
indexed per-node accepted-form typing premises, and typed child-reference plus
real-root-arrow resolution, while carrying the byte decoder's indexed no-fail
and no-`disconnect1` node exclusions. The lean generated Coq module
defines the decode-only certificate checker expression over the emitted bytes,
proves that the emitted bytes are accepted by the streaming Coq
raw-DAG decoder, proves the raw nodes have canonical root-reachable order, and
proves that the emitted bytes structurally decode to some `StructuralProgram`.
It also packages the streaming checker result as
`CompiledMultisigByteCertificateStreamingDecodeEvidence`, exposing the static
field checks, raw byte-decoder result, strict raw backreferences, canonical
order, jet whitelist, DAG well-formedness, DAG length bound, backward real-node
child references, no decoded fail nodes, no decoded `disconnect1` nodes, hidden
CMR payload uniqueness, hidden CMR 256-bit length, and closed-padding check for
the concrete artifact. The
generated module also exposes a conditional
`CompiledMultisigByteCertificateStreamingBridgeEvidence` theorem: once a
concrete CMR algebra makes the streaming checked-CMR checker accept these bytes,
Coq gets checked CMR equality to the exported CMR. The full formal bridge still
needs that concrete CMR algebra and foundation/Elements semantics before the
certificate proves the end-to-end multisig security theorem. In the current Coq
bridge, Elements jet arrows, Simplicity witness admissibility, word-node type
rules, fail rejection, reserved one-child disconnect rejection, and two-child
disconnect typing are checked locally; witness value semantics still wait on
the foundation integration.

Simplex-facing tests are named with the Simplex test marker suffix so the same
checks run under Cargo and `simplex test`.

```bash
cargo test -p simplicity-native-multisig-contracts
simplex test
```
