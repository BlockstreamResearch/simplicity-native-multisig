# Bridge implementation path

## Bridge implementation options

### Option A: Source-level bridge first

Define a small Coq semantics for the subset of SIMF/SimplicityHL used by
`multisig_n_of_3.simf`, then prove that the source program implies
`multisig_covenant_succeeds`.

The current `MultisigSourceBlocks.v` theorem already composes named
source-block premises into `multisig_covenant_succeeds`; a fuller source
semantics would discharge those premises from syntax. Its limitation is that it
still trusts the Rust/SimplicityHL compiler to preserve the source semantics.
It is not yet a complete direct proof about the compiled bytes, although the
current concrete byte certificate already discharges the artifact's static
threshold/participant side in Coq.

### Option B: Generated Coq AST/proof certificate

Extend the Rust builder or a verification tool to export:

- the compiled `ConstructNode` or `CommitNode` as a Coq definition;
- the program CMR as a checked constant;
- debug-symbol boundaries for named SIMF functions;
- optional per-function proof skeletons or certificates.

Coq then checks the exported term and proves the bridge theorem over that term.
This is the recommended practical bridge because it directly targets the
compiled node tree while keeping the proof manageable. The CMR anchors the proof
to the committed artifact, although a fully byte-level proof would still require
a Coq decoder.

### Option C: Coq byte decoder

Port or implement the Simplicity bit decoder in Coq and prove:

```coq
decode program_bytes = compiled_multisig
```

Then prove the same semantic bridge over `compiled_multisig`.

This is the strongest route because it removes the Rust exporter/compiler from
the trusted bridge. The current `SimplicityByteDecoder.v` is the beginning of
this route: it decodes the structural byte encoding, validates hidden/assertion
rules and canonical root-reachable order, and checks a 256-bit root CMR under a
supplied CMR algebra. `FoundationCmrAlgebra.v` now narrows the intended
algebra shape to the upstream foundation tag/`compress_half`/`compress`
structure. The current concrete artifact already uses the byte-decoder route
for streaming structural decode and static certificate checks. The remaining
work is to instantiate `FoundationCmrOps` with the concrete
foundation/Rust-compatible hash functions and add the Elements primitive
specifications/evaluation bridge.

### Option D: Trace/certificate checker

Generate a compact execution or symbolic-evaluation certificate from the
compiled program and have a small Coq checker validate each step against the
Elements primitive specs.

This can be a good compromise if the full compiled AST is too large to prove
against manually. The checker must be small enough to audit, and it must reject
certificates unless they imply `multisig_covenant_succeeds`.

## Recommended path

Use a staged bridge:

1. Keep the existing abstract model proof as the security theorem.
2. Add an Elements primitive module for only the jets this covenant uses.
3. Prove source-level SIMF block lemmas against the model predicate.
4. Fix the foundation dependency shell, align Coq versions, and instantiate
   `FoundationCmrOps` with the concrete Simplicity foundation/Rust CMR functions
   plus `ElementsJetCmr.v`'s checked Elements jet CMR table. Then prove the
   typed streaming checked-program run accepts the deployed artifact's exported
   CMR under `foundation_elements_cmr_algebra ops`; the direct decoded-program
   and checked-CMR projections for that specialized run are already exposed in
   `CompiledMultisigFoundationCmrEvidence.v`.
5. Use the compact indexed type artifact from `coq-typed`, tie
   `ElementsJetTypes.v` to the foundation type representation, use the narrowed
   `FoundationElementsProviders.v` obligations for allowed non-core node
   families, connect witness values during semantic evaluation, and convert the
   checked typed structural program into a foundation term.
6. Continue the stronger byte-decoder route for the actual byte artifact, using
   the existing imported constants, structural decoder, compact type artifact,
   and static certificate theorems as the artifact boundary.
7. Prove that the decoded compiled term's successful foundation evaluation
   produces the remaining semantic bridge facts: prefix/static assertion
   success, `ElementsVoteSlotsExecution`, and the final threshold assertion.

This avoids a shortcut: the proof remains checked by Coq, but the first
implementation milestone does not try to verify the whole compiler and byte
decoder at once.

## Minimal first milestone

A useful first bridge milestone is:

```coq
Elements primitive specs for the multisig jets
  + Coq model of the SIMF source blocks
  + proofs for each block listed above
  -> source_multisig_implies_model_success
```

That milestone makes the contract proof executable at the source-semantics
level. It does not yet close the compiled-byte gap, but it gives the exact
lemmas that the generated compiled-program proof will need.

The next milestone is:

```coq
decoded or exported compiled node tree has expected CMR
  + decoded or exported compiled node tree refines source block semantics
  -> compiled_multisig_implies_model_success
```

At that point, the proof is about the compiled Simplicity program up to the
remaining exporter or concrete-decoder trust boundary.

## Bottom line

The problem is not that we lack compiled Simplicity opcodes. The current proof
already imports and structurally checks those bytes, and it connects their
static parameters to the model and to the checked typed+CMR foundation root-term
path. The strongest checked theorem is now specialized to the foundation-shaped
CMR adapter surface, but the concrete upstream CMR instantiation is still open.
The remaining semantic problem is that there is no complete formal bridge from
successful execution of those opcodes to the assertion and executed vote-slot
facts consumed by the strongest checked-artifact security theorem.

The foundation gives the language and proof machinery. Our work is to add the
contract-specific Elements semantics, represent or decode the compiled program
inside Coq, and prove that successful concrete execution implies the abstract
multisig success predicate.
