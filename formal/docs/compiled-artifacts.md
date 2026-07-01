# Compiled artifact inventory

## What we have

### Contract compilation path

The native multisig builder compiles `crates/contracts/simf/multisig_n_of_3.simf`
through Simplex/SimplicityHL:

- `crates/contracts/src/multisig/builder.rs` loads `MULTISIG_SOURCE`.
- `MultisigBuilder::compile` calls `TemplateProgram::new(...).instantiate(...)`.
- The result is a `CompiledProgram`.
- `MultisigBuilder::cmr` obtains the committed program root through
  `compile()?.commit().cmr()`.
- `MultisigBuilder::compiled_certificate` now exports a
  `CompiledMultisigCertificate` containing the static parameters, canonical
  no-witness committed program bytes from `CommitNode::to_vec_without_witness`,
  the CMR computed from the same `CommitNode`, the committed root arrow, and a
  per-node type table for the encoded committed program. Its stable artifact
  form serializes threshold, participant x-only public keys, CMR hex, and
  program bytes hex as JSON. The same certificate can also be emitted as a
  complete lean Coq module defining `compiled_multisig_certificate :
CompiledMultisigByteCertificate`, so the actual compiled bytes can be imported
into Coq as constants. A separate `coq-typed` export emits a compact indexed
typed certificate: type definitions, arrow source/target indexes, per-node
arrow indexes, and a root-arrow index. `coq-typed-split <output_dir>` emits
the same certificate as the split `CompiledMultisigTypedExample*.v` module
family used by the formal build. Coq expands that artifact into a
`CompiledMultisigTypedByteCertificate` before invoking the typed checker. The
lean generated module also defines
`compiled_multisig_decoded_program` as the Coq decode-only certificate checker
applied to those constants. It also defines
`compiled_multisig_streaming_decoded_program` as the streaming certificate
checker over the same constants and proves
`compiled_multisig_streaming_decode_evidence`. That theorem packages the
concrete artifact as byte-certificate evidence checked by Coq: static field
checks, streaming raw byte decode, strict raw backreferences, canonical
root-reachable order, streaming structural decode, multisig jet whitelist,
well-formed structural DAG, DAG length bound, backward real-node child
references, no decoded fail nodes, and closed padding. The generated module
also defines
`compiled_multisig_streaming_checked_program` and proves
`compiled_multisig_streaming_bridge_evidence_if_checked_cmr`, a conditional
bridge theorem that adds checked CMR equality to the exported CMR once a
supplied concrete CMR algebra accepts the streamed artifact.

`simplicityhl/src/lib.rs` shows the shape of that artifact:

- `CompiledProgram` stores a named Simplicity program plus witness and parameter
  type metadata.
- `CompiledProgram::commit` returns a `CommitNode` with witness names removed.
- `CompiledProgram::satisfy` populates witness nodes.
- `satisfy_with_env` can prune under an `ElementsEnv`.

The runtime spending path in `crates/contracts/src/common/witness.rs` is:

```rust
program.satisfy(witness_values)
  -> satisfied.redeem().prune(env)
  -> BitMachine::for_program(&pruned)
  -> mac.exec(&pruned, env)
  -> pruned.to_vec_with_witness()
```

This is the concrete execution path the bridge proof should target.

The certificate round-trip test
`multisig::builder::tests::compiled_certificate_round_trips_through_commit_decoder`
checks the Rust-side artifact boundary: the exported bytes decode as an
Elements `CommitNode`, the decoded node has the exported CMR, and re-encoding
the decoded node produces the same bytes. It also checks that the stable JSON
artifact agrees with the in-memory certificate. A companion test checks that the
Coq module exporter contains the same threshold, participant bytes, no-witness
program bytes, and CMR bytes as the in-memory certificate.

### SimplicityHL lowering path

`simplicityhl/doc/translation.md` gives informal lowering rules from
SimplicityHL expressions into Simplicity combinators for variables, witnesses,
jets, sequencing, lets, matches, and unwrap/assert forms.

`simplicityhl/src/compile/mod.rs` implements that lowering:

- expressions compile into named `ConstructNode`s;
- variable lookup is expressed as projections out of a product-shaped scope;
- calls to `jet::...` become Simplicity jet nodes;
- `assert!`, `unwrap`, and `panic!` become assertion/fail nodes;
- the final construct node is type-finalized into a `CommitNode`.

This compiler path is not currently proved correct in Coq. It is useful
engineering evidence, but it is not itself a formal bridge.

### Coq foundation

The foundation at `/Volumes/Somebody/Desktop/Simp/simplicity/Coq` provides:

- `Simplicity/Core.v`: a typed core `Term` language and pure `eval`.
- `Simplicity/Alg.v`: algebraic semantics for core, assertions, witnesses,
  `scribe`, and the relevant parametricity/initiality lemmas.
- `Simplicity/Primitive.v`: generic primitive, jet, full-Simplicity, primitive
  tag, environment, and primitive-semantic interfaces.
- `Simplicity/Delegation.v`: the `disconnect` interface and delegator
  correctness lemmas.
- `Simplicity/MerkleRoot.v`: the concrete Coq definitions of type roots,
  commitment roots, identity hashes, and Simplicity commitment tags.
- `Simplicity/Translate.v`: bit-machine translation/correctness infrastructure.
- `Simplicity/Primitive/Bitcoin.v`: a Bitcoin-style primitive environment.

The key limitation is that `Primitive/Bitcoin.v` is not an Elements/Taproot
specification for this contract. The multisig uses Elements jets and an
`ElementsEnv`, while the Coq foundation currently has no matching
contract-specific Elements primitive module.

The foundation C side is also relevant because it is what Rust-compatible
compiled bytes follow. `C/deserialize.c` defines the bit-level DAG decoder,
including hidden-node assertion conversion, rejected fail/reserved encodings,
root-hidden rejection, canonical-order verification, and node CMR computation.
`C/typeInference.c` defines the typing constraints for every decoded DAG node.
`C/elements/primitive.c` and the generated `primitiveJetNode.inc` define each
Elements jet's source type, target type, CMR, and cost.

### Checked bridge artifacts in this repo

`ElementsJets.v` now fixes the proof scope to the exact Elements jets used by
`multisig_n_of_3.simf`. It records the Rust `(code, width)` pairs, provides an
executable decoder for that jet subset, and declares the semantic interface
needed by later bridge lemmas. It also defines the whitelist predicate
`multisig_elements_jet` and proves that every `ElementsJet` constructor is in
that explicit list.

`ElementsJetSemantics.v` starts the contract-specific semantic bridge for that
interface. It does not define a hidden evaluator; instead it records explicit
laws that a later Elements primitive evaluator must satisfy and proves
source-block facts from those laws. The checked lemmas currently cover
`verify`, `ensure_zero_bit`, failed `eq_256` participant comparisons,
threshold `le_32` assertions, prefix/current-index assertions, no-carry
`add_32`, the final minimum-input `le_32` assertion, and an
`ElementsEnvTxRelation` connecting environment lookups to the abstract
transaction lists used by `MultisigSecurity.v`.

`ElementsJetCmr.v` adds the concrete CMR constants for that same whitelist,
copied from `/Volumes/Somebody/Desktop/Simp/simplicity/C/elements/primitiveJetNode.inc`.
The constants are Coq definitions, not axioms, and the audit checks that every
entry is a 32-byte value and therefore a 256-bit CMR bitstring. It also exposes
`with_elements_jet_cmr`, which will let the foundation-backed core CMR algebra
reuse the checked Elements jet CMR table.

`CmrWellFormed.v` packages the 256-bit-output contract used by the checked CMR
decoder, and `FoundationCmrAlgebra.v` packages the foundation-shaped CMR
operation surface that a concrete upstream `Digest`/`MerkleRoot` instantiation
must fill. The adapter mirrors the upstream tag, `compress_half`, and
`compress` structure, with checked lemmas for assertion case-tag CMRs,
two-child disconnect CMRs, and the Elements jet CMR table override, but it
deliberately does not define the SHA256/tag constants itself.

`ElementsJetTypes.v` adds the matching source/target type table for the same
whitelist, copied from the upstream `primitiveJetNode.inc` source/target
indices and `primitiveInitTy.inc` type definitions. The types are represented as
compositional `BridgeType` values, and the audited theorem
`elements_jet_typecheck_accepts_declared_arrow` proves that `TypedBridge.v`'s
jet-node checker accepts the declared arrow for each whitelisted jet.

`SimplicityByteDecoder.v` now provides the first Coq byte-level artifact: an
executable decoder for bytes into raw Simplicity nodes, including MSB-first byte
expansion, C-compatible positive natural decoding bounded by
`simplicity_decodeUptoMaxInt`'s `2^31 - 1` maximum, bounded backreferences,
structural node tags, hidden CMR payloads, words, witnesses, and the multisig
Elements jet subset. It rejects DAG length prefixes above the deployed
`DAG_LEN_MAX = 8000000` bound and rejects the no-witness fail opcode, matching
the C decoder's `SIMPLICITY_ERR_FAIL_CODE` behavior for serialized no-witness
DAGs. Its raw decoder proves that every accepted child reference is a strict
backward reference to an earlier raw node. It also mirrors
`simplicity_closeBitstream`: after decoding the final node it accepts
only zero padding shorter than one byte, so a non-zero padding bit or a whole
extra zero byte is rejected. It also contains a raw-to-structural validation
pass that
mirrors the Rust decoder's hidden-node rules: hidden nodes cannot be roots or
ordinary children, case nodes with one hidden child become assertions, case
nodes with two hidden children are rejected, duplicate hidden CMR payloads are
rejected, and every decoded hidden CMR payload is proved to be exactly 256 bits.
Accepted structural programs now expose this as
`structural_program_hidden_cmrs_unique` and
`structural_program_hidden_cmrs_256` proofs over hidden payloads. The
decoder also checks canonical root-reachable postorder, so
unused raw nodes and raw node lists that do not match the root traversal order
are rejected. It also computes the decoded structural program's root CMR under
an explicit CMR algebra and proves that the byte decoder plus CMR verifier only
accepts programs whose recomputed root equals the expected root under that
algebra. A stricter checked verifier rejects any computed or expected CMR that
is not exactly 256 bits. The structural decoder also exposes
`structural_program_jets` and proves `structural_program_jets_are_multisig_subset`,
so accepted byte programs have a named Coq proof that all decoded jets are drawn
from the multisig whitelist. It also defines and proves
`structural_program_dag_well_formed`: accepted structural programs have a real
node at the root, and every child reference points backward to an already
converted real node rather than to a hidden placeholder or future node. The
boolean invariant is also exposed through
`structural_program_dag_well_formed_child_references`, a Prop-level theorem
stating that every child of every decoded real node resolves to an earlier real
node. The decoder now also proves that accepted decoded byte programs contain no
`SFail` structural nodes, no `SDisconnect1` nodes from the reserved one-child
disconnect code, no duplicate hidden CMR payloads, and no hidden CMR payload
with a non-256-bit length.

`TypedBridge.v` adds a checked structural type-table layer. Given a decoded
structural program and an exported per-node type table, Coq checks the typing
rules for core combinators directly and requires hidden CMR placeholders to have
no type entry. It delegates jets, witnesses, words, fail, and disconnect forms
to explicit hook functions. `ElementsJetTypes.v` now instantiates the jet-arrow
hook for the whitelisted Elements jets, Simplicity witness admissibility, the
word type rule (`Unit -> TWO^(2^n)` with a checked compact bit length), fail
rejection, reserved one-child disconnect rejection, and the two-child disconnect
type rule. Witness value decoding, semantic evaluation, and the connection from
`BridgeType` to the Simplicity foundation type representation are still open.
The typed bridge now exposes an atom-freeness predicate for bridge types, and
the compact certificate layer proves that atom-free compact type definitions
expand to atom-free type tables and root arrows. The concrete compiled typed
artifact is audited as atom-free, so its type shape uses only Unit/Sum/Prod
constructors. `BridgeTypeTranslation.v` then proves that any such atom-free
type table translates into any Unit/Sum/Prod type algebra, and the concrete
compiled typed certificate is audited to translate for every such algebra.
`FoundationTypes.v` imports the standalone upstream `Simplicity.Ty` file and
audits that same concrete certificate against the actual foundation `Unit`,
`Sum`, and `Prod` constructors. `FoundationCore.v` also imports standalone
upstream `Simplicity.Core` and proves that checked typed evidence for a pure
core node form yields an actual foundation `Term`, conditional on child
foundation terms. It also recursively builds child-term providers from checked
typed prefixes and packages typed-byte root term construction behind explicit
non-core primitive provider obligations. `FoundationElementsProviders.v` narrows
that obligation for the multisig typed-certificate hook profile to assertion,
Elements jet, witness, word, and two-child disconnect providers, while proving
fail and reserved one-child disconnect cases impossible from the hook
rejections. `CompiledMultisigFoundation.v` applies that generic theorem to the
actual generated compact typed multisig certificate, so the concrete decoded
artifact now has named conditional foundation-root term theorems against both
the generic provider and the narrowed Elements provider family. It also applies
the same root-term construction to both the compact typed checked-CMR bridge
evidence path and the direct successful typed streaming checked-program result,
anchoring that theorem to bytes, the exported type table, and the declared CMR
check. `CompiledMultisigFoundationSecurity.v` composes the
checked typed+CMR foundation entry point with the concrete artifact security
theorem, so the current strongest checked-artifact theorem returns a foundation
root term and the full model security property from a successful typed streaming
checked-program run when the semantic static/prefix/minimum assertion-success
facts, executed vote slots, and final vote-threshold assertion are supplied.
`CompiledMultisigFoundationCmrSecurity.v` specializes that strongest theorem to
the `foundation_elements_cmr_algebra ops` adapter, so the remaining CMR premise
is a successful checked run with a concrete `FoundationCmrOps` implementation
rather than an arbitrary local CMR algebra.
`CompiledMultisigFoundationCmrEvidence.v` exposes the lighter byte-decoder side
of that same specialized checked run: the concrete artifact bytes stream-decode
to the returned program, and the checked CMR computation under
`foundation_elements_cmr_algebra ops` equals the exported artifact CMR.
The typed evidence
also proves that the exported table has exactly one
entry per decoded node, every real node has a `Some` arrow, every hidden
placeholder has `None`, and the root is a real node with the declared root
arrow. When combined with the byte decoder's child-reference theorem, it also
proves every child reference resolves to an earlier real node with a typed
arrow. The typed byte evidence now carries the byte decoder's no-fail and
no-`disconnect1` facts plus indexed theorems excluding `SFail` and
`SDisconnect1` nodes from the accepted artifact. The
checker also has a Prop-level `structural_node_type_evidence`
soundness theorem that mirrors each accepted node form's typing premises. The
aggregate typed evidence stores the corresponding recursive proof object, and
`typed_program_node_has_type_evidence` recovers the premise for any indexed real
node. The theorem
`check_typed_structural_program_with_byte_evidence` packages typed evidence
together with the byte decoder's DAG and child-reference facts.

`MultisigSourceBlocks.v` starts the source-to-model bridge with checked lemmas
for individual SIMF blocks. The first theorem proves that the three
`ensure_distinct_participants` equality failures imply `NoDup` for the three
declared participants. The static-parameter theorem then combines that
distinctness result with the threshold checks to produce the static premises
expected by `multisig_covenant_succeeds`: exactly `participant_count`
participants, no duplicate participants, and `1 <= threshold <=
participant_count`. The source-block composition theorem packages those static
checks together with the multisig prefix checks, input-availability check, and
`CountVotes` block, and proves the actual model predicate
`multisig_covenant_succeeds`.

`CompiledMultisigExample.v` specializes those source/model lemmas to the
concrete generated artifact. It exposes `compiled_multisig_threshold` and the
three decoded participant keys from `compiled_multisig_certificate`, proves
that those concrete values satisfy the static source checks, and then proves
that explicit prefix, `CountVotes`, and threshold-count premises imply
`multisig_source_blocks_succeed` and `multisig_covenant_succeeds` for the
concrete participant set. It also proves concrete artifact corollaries whose
conclusions are the model's threshold-distinct-declared-participant
authorization theorem and full security property under those same dynamic
premises.

`MultisigCertificate.v` defines the Coq-side byte certificate format matching
the Rust artifact fields: threshold, three participant x-only public keys,
program bytes, and CMR bytes. Its decode-only checker validates threshold
bounds, participant count and key lengths, byte ranges, and CMR byte length
before calling the checked structural byte decoder. Its full checker adds
`decode_structural_program_bytes_with_checked_cmr`. The decode-only and
streaming decode evidence theorems package static certificate facts, the raw
byte-decoder result with strict raw backreferences and canonical root-reachable
order, decoded structural program, jet whitelist, DAG well-formedness, DAG
length bound, backward real-node child references, no decoded fail nodes,
hidden CMR payload uniqueness, hidden CMR 256-bit length, and closed padding.
The streaming variant uses the cursor decoder that can compute over the real
compiled artifact in Coq. Both the original and streaming checked-CMR checker
soundness theorems state that checked CMR recomputation returns the certificate
CMR bits and that the CMR is 256 bits. Separate static-field
soundness lemmas expose the model-facing facts later bridge proofs need: the
threshold is in the `1..participant_count` range, exactly `participant_count`
participant keys are present, each key is 32 bytes, and all exported byte lists
are byte-range checked. The aggregate theorem
`check_compiled_multisig_byte_certificate_bridge_evidence` packages the current
byte-level bridge contract with checked CMR equality/length. The companion theorem
`check_compiled_multisig_byte_certificate_typed_bridge_evidence` composes that
byte-certificate evidence with the typed structural checker, provided an
exported type table and hook instantiation check successfully.

`MultisigTypedCertificate.v` makes that composition a first-class certificate
checker. A `CompiledMultisigTypedByteCertificate` contains the byte certificate,
an exported per-node type table, and the expected root arrow. Its streaming
decode-only checker first runs the byte-certificate checker without CMR, then
runs `TypedBridge.v` with the Elements hook profile from `ElementsJetTypes.v`.
Its CMR-checked checker does the same after the streaming checked-CMR
byte-certificate checker. The audited evidence theorems package those facts as
typed streaming decode or bridge evidence, including the typed table's length,
real/hidden node shape, typed child-reference resolution, real-root-arrow
checks, indexed no-fail-node and no-`disconnect1` exclusion, and indexed
per-node Prop-level typing soundness.

These files and the Rust certificate exporter do not yet complete the
compiled-program theorem. The exporter now provides both machine-readable JSON
and a Coq constants module, and the generated concrete module proves streaming
decode evidence for the actual compiled bytes. It also exposes a conditional
streaming checked-CMR bridge theorem and a direct security composition from a
successful typed streaming checked-program run. Instantiating that run with the
foundation/Rust-compatible CMR algebra is still required. These pieces replace
part of the planned exporter trust boundary with checked Coq code and give a
stable Rust artifact boundary, but
concrete foundation/Rust-compatible CMR hash instantiation, concrete primitive
providers for assertion/jet/witness/word/disconnect nodes, witness decoding, and
symbolic evaluation that produces the semantic assertion and executed-vote facts
consumed by `multisig_covenant_succeeds` are still required.

The concrete foundation CMR instantiation was tested against
`/Volumes/Somebody/Desktop/Simp/simplicity/Coq/Simplicity/MerkleRoot.v`. That
module provides `hash256`, `compress`, `compress_half`, and the Simplicity
commitment tags needed to instantiate the local CMR algebra. The dependency
boundary is now precise: a Coq 9.1 probe can build CompCert but fails to find
`sha.SHA256`, while the upstream Coq 8.17 `vst` derivation does compile the VST
SHA Coq proofs and then fails in its Darwin `postBuild` step because it invokes
`gcc -c sha/sha.c -o sha/sha.o` and `gcc` is not present. Until that shell is
fixed and this project is built in the same Coq version as the foundation, the
checked bridge in this repo remains foundation shape-compatible but not yet
foundation-backed for core CMR hashing.
