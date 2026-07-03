# Compiled-program bridge research

> **Status (2026-07-03).** Kept as design history; the layered plan below is
> now largely realized, with layer numbers mapping to the current tree as
> follows. Layers 1-3 (artifact identity, byte decoding, typing) are complete
> and stronger than planned: the CMR gap flagged in layer 2 was closed by a
> self-contained FIPS-proven SHA-256 algebra instead of the upstream
> `Digest/MerkleRoot` instantiation (`CompiledMultisigRealCmr.v`), and the
> checked run is discharged outright (`CompiledMultisigRealSecurity.v`).
> Layer 4 (foundation term construction) exists behind provider obligations.
> Layer 5 (primitive semantics) is implemented executably in
> `ElementsConcreteJets.v`, and the deployed bytes now run inside Coq with
> proven accept/reject behavior on concrete scenarios
> (`CompiledMultisigExecution.v`). Layer 6 — symbolic execution/refinement
> for arbitrary environments — is the one remaining open obligation; layer 7
> already consumes its conclusion. Current state: `README.md`.

This note answers the concrete bridge question: if we already have a compiled
multisig program represented as Simplicity bytes/opcodes, what is still missing
before the Coq proof is a proof about that compiled artifact?

## Short answer

The compiled program is the artifact we want to prove things about.  It is now
partly a Coq object with Coq theorems attached to it: Coq imports the concrete
byte certificate, decodes and validates it structurally, checks its exported
static threshold/participant fields, checks the compact typed artifact including
the declared CMR through a Coq checker entry point, specializes the strongest
checked theorem to a foundation-shaped CMR adapter, and composes those static
facts with semantic assertion and executed-vote premises into the abstract
covenant model and the model security theorem.

The current proof in `MultisigSecurity.v` proves the contract-level security
property for an abstract model:

```coq
multisig_covenant_succeeds ... -> multisig_success_security_property ...
```

The still-missing bridge theorem is the earlier implication from successful
foundation execution to those dynamic premises:

```coq
concrete compiled Simplicity program succeeds under an Elements environment
  -> multisig_covenant_succeeds ...
```

Only after that theorem is composed with the existing concrete-artifact
security theorem do we have an end-to-end statement about the compiled covenant.

## The precise problem with "we have opcodes"

The opcode byte string answers only one question: which concrete Simplicity DAG
did the Rust/SIMF toolchain emit?  Formal verification needs a chain of Coq
statements whose conclusion is the covenant property.  The missing parts are
not about trusting that bytes exist; they are about proving what those bytes
mean.

The intended no-shortcut bridge has these layers:

1. **Artifact identity.**  Coq imports the exact exported no-witness program
   bytes, static participants, threshold, root arrow, type table, and CMR.
2. **Byte decoding.**  Coq decodes the bytes into a structural Simplicity DAG,
   checks padding, hidden/assertion rules, canonical order, child references,
   no fail nodes, no reserved `disconnect1`, multisig-only Elements jets, and
   CMR equality under a concrete CMR algebra. The current strongest checked
   theorem already requires that algebra through the foundation-shaped
   `FoundationCmrOps` adapter; the concrete `Digest/MerkleRoot` instantiation
   is still missing.
3. **Typing.**  Coq checks the exported per-node type table against that decoded
   DAG, including the root arrow and the source/target types of every
   whitelisted Elements jet.
4. **Foundation term construction.**  Coq turns the typed structural DAG into
   the upstream Simplicity foundation's term representation under explicit
   primitive-provider obligations.  Pure core nodes are bridged to
   `Simplicity.Core.Term`, and the compiled multisig theorem now reaches a
   foundation root term when assertion, jet, witness, word, and disconnect
   providers are supplied. The next no-shortcut target is to instantiate those
   providers with concrete foundation semantics rather than local placeholders.
5. **Primitive semantics.**  Coq specifies the Elements environment and each
   used Elements jet: transaction introspection, SHA256 context operations,
   Taproot/taptweak construction, Schnorr verification, arithmetic/comparison
   jets, and `verify`.
6. **Symbolic execution / refinement.**  Coq proves that if the constructed
   Simplicity term succeeds under that Elements environment and witnesses, then
   the abstract model predicate `multisig_covenant_succeeds` holds.
7. **Security theorem composition.**  The existing model theorem then yields
   the final claim: at least `threshold` distinct declared participants
   authorized the batch, and the signed message commits to the multisig input
   prefix plus proposed outputs.

So the compiled opcodes are necessary input to the proof, not the proof itself.
They are now formally useful up to byte decoding, typing, foundation-term
construction under explicit primitive providers, and concrete security
composition from a successful typed streaming checked-program run under semantic
assertion and executed-vote premises. The checked run is now specialized to the
foundation-shaped CMR adapter surface, and the direct decoded-program plus
checked-CMR equalities for that specialized run are now exposed separately from
the heavy security theorem. The remaining CMR gap is a concrete
`FoundationCmrOps` implementation from the foundation/Rust-compatible
`Digest/MerkleRoot` functions plus the proof that the deployed artifact is
accepted with it. The remaining semantic gap is to interpret successful
foundation execution of the concrete artifact and derive the prefix/static
assertion facts, `ElementsVoteSlotsExecution`, and final threshold assertion
that the strongest checked-artifact security theorem consumes.


## Detailed notes

The long-form research notes are split by responsibility:

- [Compiled artifact inventory](docs/compiled-artifacts.md) describes the Rust/SimplicityHL compilation path, Coq foundation, and checked artifacts currently in this repository.
- [Bridge theorem targets and obligations](docs/bridge-targets.md) records what compiled opcodes do not prove by themselves, the byte artifact shape, the target theorem, and multisig-specific proof obligations.
- [Bridge implementation path](docs/bridge-path.md) compares implementation options and captures the recommended milestone path.
