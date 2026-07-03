# Formal verification of the native multisig

A Rocq (Coq) audit of the Simplicity native multisig, from an abstract
security model all the way down to the deployed compiled bytes. Everything is
axiom-free (`Print Assumptions` reports "Closed under the global context" for
every named theorem) and independently re-checked by the `rocqchk` kernel
checker.

## What is machine-checked

The chain, from model to deployed bytes; each link names its top theorem:

1. **Model security** — if the modeled covenant succeeds, at least
   `threshold` *distinct declared* participants authorized the spend, each
   with a valid signature over
   `participant_message vote_executable_leaf_hash base_message` and a
   transaction input committed to the vote Taproot script
   (`multisig_success_security_property`, `MultisigSecurity.v`).
2. **Source blocks imply the model** — the SIMF building blocks (participant
   distinctness, threshold bounds, prefix/minimum-input checks, vote
   counting) imply the model predicate
   (`multisig_source_blocks_imply_model_success`, `MultisigSourceBlocks.v`).
3. **Artifact identity, no exporter trust** — the deployed certificate bytes
   stream-decode to a well-formed, type-checked structural program using only
   the whitelisted jets, and its commitment Merkle root — recomputed by a
   self-contained SHA-256 proven against the FIPS 180-4 vectors — equals the
   exported CMR byte-for-byte
   (`compiled_multisig_real_cmr_matches_exported`,
   `CompiledMultisigRealCmr.v`).
4. **Artifact security with the checked run discharged** — the full streaming
   byte+type+CMR checker provably *succeeds* on the deployed certificate
   under the concrete SHA-256 algebra, and the strongest security theorem is
   instantiated with that fact; the remaining premises are purely semantic
   (`compiled_multisig_real_artifact_security_from_executed_votes`,
   `CompiledMultisigRealSecurity.v`).
5. **Artifact execution behavior** — the deployed bytes *execute inside Coq*
   under a concrete jet interpretation, and acceptance is
   signature-, threshold-, commitment- and message-gated: the program accepts
   an honest two-vote scenario and rejects the no-valid-signature,
   below-threshold, uncommitted-vote, and tampered-outputs variants; no run
   reaches the evaluator's structural-error state
   (`deployed_multisig_execution_behavior`, `CompiledMultisigExecution.v`).

## Trust boundaries — what is NOT proven

Stated explicitly so the claims above are not over-read:

- **Universal execution refinement (open):** "for *all* environments and
  witnesses, evaluation success implies the vote-execution premises" is not
  yet a theorem. The execution results in (5) are closed computations on
  concrete scenarios; the security theorem in (4) still takes the semantic
  vote-execution premises as hypotheses.
- **Cryptography is abstract:** BIP-0340/elliptic-curve arithmetic is not
  interpreted. The model uses an abstract `signature_valid`; the executable
  jets use an explicit table of valid (key, message, signature) triples —
  the same abstraction point. Taproot tweaking is modeled as its tagged-hash
  commitment; the final EC point addition is abstracted.
- **Consensus fidelity is pinned only where cross-checkable:** jet CMR bytes
  (upstream `primitiveJetNode.inc`), SHA-256 (FIPS vectors), Simplicity CMR
  tag IVs (rust-simplicity, validated against the published
  `BITS = injl/injr(unit)` constants), and decoder limits
  (`2^31 - 1` naturals, `DAG_LEN_MAX`, close-padding, canonical order). The
  executable jet semantics beyond that (e.g. exact Elements tag strings) is
  internally consistent rather than consensus-pinned.
- **SIMF ↔ Coq correspondence:** `MultisigSourceBlocks.v` is a hand-written
  formalization of `multisig_n_of_3.simf`, related by inspection, not by a
  verified compiler.

## Building and auditing

Requires Rocq 9.1 with the stdlib. Serial build (`make` never needs `-j`):

```sh
cd formal
make          # compile every module
make audit    # full audit: Print Assumptions for every named theorem
              # (all must be closed) + rocqchk kernel sweeps
```

Without a system installation:

```sh
nix-shell --pure -p rocq-core rocqPackages.stdlib gnumake findutils coreutils \
  --run 'cd formal && make audit'
```

The audit takes ~35 minutes and peaks under ~1.2 GB.

**Proof-style constraints (memory-critical).** Files that state theorems over
the concrete artifact must NOT enable `Set Implicit Arguments`/`Set Strict
Implicit`, should end proofs with `pose proof ... as H. exact H.` rather than
`exact (<lemma> <args>)`, and should keep shared concrete facts in opaque
`Lemma`s rather than transparent `Definition`s. Violating this makes Rocq
9.1's Qed-time kernel conversion lose sharing and symbolically re-run the
byte decoder inside the kernel (observed: >26 GB RSS per theorem). See the
header comments in `CompiledMultisigFoundation*.v`.

## Layout

| Layer | Files | Contents |
|---|---|---|
| Security model | `MultisigModel.v`, `MultisigSecurity.v` | Transaction/participant/vote model; top security theorems |
| Source bridge | `MultisigSourceBlocks.v`, `ElementsJetSemantics.v`, `ElementsJetEnvironment.v`, `ElementsJetSemanticsInhabited.v` | SIMF block lemmas; jet assertion laws; environment-to-model relation; semantic-spec consistency witness |
| Byte decoder | `SimplicityByteDecoder*.v` (16 files) | Executable decoder: bits/cursor parsing, canonical raw order, hidden/assertion conversion, DAG well-formedness, close-padding, CMR verification hooks |
| Typed bridge | `TypedBridge*.v`, `ElementsJetTypes.v`, `BridgeTypeTranslation.v` | Per-node type-table checker with hooks; whitelisted jet arrows; Unit/Sum/Prod type-algebra translation |
| Jet tables | `ElementsJets.v`, `ElementsJetCmr.v` | The 25-jet whitelist: codes, decoder, consensus CMR bytes |
| Concrete CMR | `Sha256Core.v`, `SimplicityCmrSha.v`, `SimplicityCmrAlgebra(Wf).v`, `CmrWellFormed.v` | Self-contained SHA-256; Simplicity tag/compress layer; concrete well-formed CMR algebra; checked/unchecked agreement |
| Foundation adapters | `FoundationTypes.v`, `FoundationCore*.v`, `FoundationElementsProviders.v`, `FoundationCmrAlgebra.v` | Adapters into vendored upstream `Simplicity.Ty`/`Simplicity.Core`; term-provider interfaces; foundation-shaped CMR adapter |
| Certificate plumbing | `MultisigCertificate*.v`, `MultisigTypedCertificate*.v` | Certificate records, shape checks, streaming byte/typed/CMR checkers, aggregate evidence theorems |
| Deployed artifact (generated data) | `CompiledMultisigByteData.v`, `CompiledMultisigTypedExample{TypeDefs,ArrowDefs*,TypeTable*,Data}.v` | Exporter-generated constants: bytes, CMR, compact type/arrow tables. Regenerate with the exporter; byte-identical to its output |
| Deployed artifact (proofs) | `CompiledMultisigExample(Core).v`, `CompiledMultisigTypedExample.v`, `CompiledMultisigFoundation*.v`, `CompiledMultisigReal*.v` | Hand-maintained: decode/type/CMR discharge, foundation-term entry points, security composition, the real-CMR and real-security capstones |
| Executable semantics | `SimplicityStructuralEval.v`, `ElementsConcreteJets.v`, `CompiledMultisigExecution.v` | Big-step evaluator; concrete executable jets; deployed-bytes accept/reject execution theorems |

Documentation: `AUDIT.md` (audit process), `FOUNDATION_PLAN.md` and
`BRIDGE_RESEARCH.md` and `docs/` (design history), `GENERALIZATION.md`
(extraction plan toward a reusable, contract-agnostic verification kit).

## Regenerating the deployed-artifact data

The Rust exporter emits **data only** (never proof text — proofs are living
Coq code owned by this tree):

```sh
cargo run -p simplicity-native-multisig-contracts \
  --example export_multisig_certificate -- \
  coq-typed-split <output_dir> <threshold> \
  <participant1_xonly_hex> <participant2_xonly_hex> <participant3_xonly_hex>
```

This regenerates `CompiledMultisigByteData.v` and the
`CompiledMultisigTypedExample*` data-module family, byte-identical to the
checked-in files for the deployed parameters. `json` and `coq` (byte data
module only) formats are also available.

## Remaining work

- **Symbolic execution refinement (the main open item):** prove that
  evaluator success on the deployed program implies the vote-execution and
  assertion premises for *abstract* environments/witnesses, turning the
  execution-scenario evidence into a universal theorem.
- **Crypto-jet semantic laws:** relate `sem_bip_0340_verify`,
  tapbranch/taptweak and SHA jets to the model's abstract predicates.
- **Decoder `nat` → `N` migration:** the decoder pipeline is unary-`nat`
  based, which forces `lazy` and forbids `vm_compute`; migrating unlocks
  fast closed computations before scaling to larger contracts.
