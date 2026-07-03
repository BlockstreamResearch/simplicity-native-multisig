# Generalizing this formal audit into a reusable Simplicity verification kit

This tree verifies one contract (the native multisig), but most of it is
contract-agnostic Simplicity infrastructure. This document maps what can be
extracted — e.g. into BlockstreamResearch/smplx — so that anyone can formally
verify a Simplicity contract starting from its compiled program, and what must
stay per-contract.

Numbers below refer to the current 78-file `formal/` tree (all audited,
axiom-free, `rocqchk`-verified, Rocq 9.1).

## The reusable pipeline (what a contract author would get)

```
smplx SDK (Rust)                          Coq/Rocq library
----------------                          ----------------
CompiledProgram                           1. byte decoder + DAG well-formedness
  └─ export coq-cert ──────────────────►  2. per-node type checker (hooks)
     (bytes, compact type defs,           3. self-contained SHA-256 CMR
      arrow defs, type table,                (byte-pinned to rust-simplicity)
      root arrow, CMR)                    4. executable evaluator + concrete jets
                                          5. generic theorem:
                                             "checker accepts ⟹ bytes decode to P,
                                              P well-typed, CMR(P) = declared"
                                          6. scenario harness: accept/reject
                                             theorems by closed computation
Contract author writes (per contract):
  model.v (security model) + bridge.v (source blocks → model) + scenarios.v
```

## Layer 1 — Certificate format and Rust exporter (mostly done, needs un-multisig-ing)

- `crates/contracts/src/multisig/builder/coq_types.rs` interns rust-simplicity
  `Final`/`FinalArrow` types into the compact indexed artifact
  (`CompactBridgeTypeDef` defs, arrow defs, per-node type table). Nothing in
  the interning is multisig-specific; only the entry point
  (`CompiledMultisigCertificate`) is. Extract as a generic exporter over any
  `CompiledProgram`/`CommitNode` and expose it as an smplx SDK command
  (`smplx export coq-cert`). Chunked-module emission included.
- Design rule learned here: the exporter emits DATA ONLY (byte certificate
  record, type/arrow/table modules, compact typed certificate record).  It
  must never emit proof text: proofs are living, hand-maintained Coq code, and
  a generator that embeds them as string constants silently drifts from the
  audited tree (this repo's generator had already diverged before it was
  trimmed to data-only).  On first scaffold the tool may emit a one-time
  proof-template file, clearly marked as never-regenerated.
- The Coq-side certificate record (`MultisigCertificateCore.v`) couples the
  generic part (program bytes + declared CMR) with contract parameters
  (threshold, participants). Generalize to
  `{ cert_program_bytes; cert_cmr }` plus an opaque contract-parameter
  extension, so the decode/type/CMR pipeline never mentions the contract.

## Layer 2 — Generic Coq verification core (~35 files, drop-in)

Fully generic today (no multisig content in definitions):

- Byte decoder and structural facts: `SimplicityByteDecoder*.v` (14 files) —
  bit/cursor parsers, canonical-order raw decode, hidden-CMR uniqueness,
  DAG well-formedness, close-padding, decode determinism, streaming and
  non-streaming paths.
- Typed checker: `TypedBridge*.v` — per-node arrow checking parameterized by
  `TypeHooks` (jet arrows, witness/word/fail/disconnect policies).
- CMR: `Sha256Core.v` (FIPS-vector-proven SHA-256), `SimplicityCmrSha.v`
  (tag IVs byte-pinned to rust-simplicity `cmr.rs`, validated against the
  published `BITS = injl/injr(unit)` constants), `SimplicityCmrAlgebra(Wf).v`,
  `CmrWellFormed.v` (checked/unchecked agreement).
- Executable semantics: `SimplicityStructuralEval.v` (value universe,
  fueled DAG evaluator, EFail vs EStuck separation).
- Upstream adapters: `FoundationTypes.v`, `FoundationCore*.v`,
  `BridgeTypeTranslation.v` (atom-free bridge types → `Simplicity.Ty`,
  core node forms → `Simplicity.Core.Term`).

Generic in structure, multisig-named (rename + re-parameterize when
extracting): the compact-typed-certificate expansion and the streaming
checked-program pipeline currently living in `Multisig*Certificate*.v`, and
the aggregate soundness/bridge-evidence theorems. These are the "generic top
theorem" of the kit; today they are stated over the multisig certificate
record only because of Layer 1's record coupling.

## Layer 3 — Jet layer (the main scaling work)

Today the jet universe is the 25-jet multisig whitelist:

- `ElementsJets.v` (codes + decoder), `ElementsJetTypes.v` (arrows),
  `ElementsJetCmr.v` (consensus CMR bytes), `ElementsConcreteJets.v`
  (executable interpretations: real streaming SHA-256 in the exact Ctx8
  buffer encoding, taproot tagged-hash constructions, env lookups, table
  gated BIP-0340).

All four are table-shaped. For arbitrary contracts, generate them from the
same source the C implementation uses (`primitiveJetNode.inc`): jet code,
source/target type, CMR bytes per jet — emitted by the exporter per contract
(the whitelist pattern keeps audits small) or shipped once as the full
Elements table. The concrete interpretations grow jet-family by jet-family;
the multisig set already covers arithmetic/comparison, optional-word env
introspection, streaming SHA-256, and taproot commitments.

Honest boundaries that carry over to any contract: BIP-0340/EC arithmetic is
interpreted as an explicit valid-triple table (the same abstraction as a
model-level `signature_valid`), and jet fidelity to Elements consensus is
pinned only where cross-checkable (CMR bytes, FIPS vectors, rust-simplicity
IVs).

## Layer 4 — Per-contract (the worked example to imitate)

Stays with each contract; the multisig files are the template:

- Security model + theorem: `MultisigModel.v`, `MultisigSecurity.v`.
- Source-block bridge: `MultisigSourceBlocks.v`, `ElementsJetSemantics.v`,
  `ElementsJetEnvironment.v`.
- Instantiations over the exported artifact: `CompiledMultisig*.v`
  (decode/type/CMR discharge, foundation-term entry points, security
  composition, and the concrete execution scenarios of
  `CompiledMultisigExecution.v`).

## Also worth upstreaming independently

- The audit harness pattern: serial builds, `Print Assumptions` over every
  named theorem, `rocqchk` kernel sweeps (`Makefile` `audit` target).
- The Rocq 9.1 Qed memory pathology and its avoidance rules (see the
  PROOF-STYLE comments in `CompiledMultisigFoundation*.v`): with
  `Set Implicit Arguments`/`Set Strict Implicit`, Qed-time kernel conversion
  can lose sharing and re-run concrete heavy computations (>26 GB observed);
  a two-`Set`-lines minimal repro exists and should be reported to
  rocq-prover/rocq.
- Engineering note for larger contracts: the decoder pipeline is unary-`nat`
  based (`byte := nat`, `natural_max := 2^31 - 1`), which forces `lazy` and
  forbids `vm_compute`. Migrating decoder arithmetic to `N` should be done
  as part of extraction, before scaling to bigger programs.

## Suggested extraction order

1. Split the generic Coq core (Layers 2 + 3 tables + evaluator) into a
   contract-neutral package (own `_CoqProject`, e.g. `simplicity-artifact-verify`),
   renaming `Multisig*Certificate*` plumbing to certificate-neutral names and
   decoupling the certificate record from contract parameters.
2. Move the Rust exporter into the smplx SDK as a generic command over any
   compiled program; emit the jet whitelist tables per contract.
3. Do the `nat` → `N` decoder migration (unlocks `vm_compute` for all closed
   computations).
4. Ship the multisig tree as the reference example: model + bridge +
   scenario files against the extracted kit, with the full audit in CI.
