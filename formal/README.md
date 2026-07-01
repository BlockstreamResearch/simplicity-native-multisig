# Formal multisig proof

This directory contains a Coq proof of the core multisig covenant security
property.

The proof models the contract logic at the covenant boundary. Cryptographic
and Elements/Taproot primitives are intentionally abstract: the model assumes
predicates/functions for BIP-0340 verification, hash construction, and the vote
Taproot script hash. This matches the current proof boundary in the Simplicity
foundation: Coq has the core semantics, while the Elements jet specifications
needed by this contract still need to be mirrored into Coq.

The top-level theorem is `multisig_success_security_property` in
`MultisigSecurity.v`. It combines the authorization, Taproot commitment, and
base-message prefix/output commitments.
The reusable transaction, participant, signature, and covenant model is in
`MultisigModel.v`; `MultisigSecurity.v` now focuses on the security statements.

It proves that if the modeled multisig covenant succeeds, then there is a list
of counted vote slots whose length is at least `threshold`; the counted
participants are distinct; and every counted slot:

- belongs to a declared participant entry,
- has a valid signature over
  `participant_message vote_executable_leaf_hash base_message`, and
- has a corresponding transaction input whose script hash is the vote Taproot
  commitment for the same signature and executable leaf.

The model includes the multisig covenant's participant uniqueness checks as
`NoDup participants`, so the top-level theorem proves the distinct-participant
reading directly. The companion theorem
`multisig_success_authorizes_threshold_distinct_declared_participants` exposes
that part of the claim separately.

The integration plan for connecting this model proof to the Simplicity
foundation is in `FOUNDATION_PLAN.md`. The compiled-program bridge research is
in `BRIDGE_RESEARCH.md`.
The proof-integrity audit is in `AUDIT.md`.

Bridge artifacts now checked by Coq:

- `ElementsJets.v` defines the exact Elements jet subset used by
  `multisig_n_of_3.simf`, its Rust bit-encoding codes, an executable decoder
  for that subset, and the semantic interface those jets must satisfy. It also
  exposes the whitelist predicate used by later byte-decoder proofs.
- `ElementsJetSemantics.v` records explicit semantic laws for that whitelisted
  interface and proves the first source-block bridges from successful jet-level
  assertions: `verify` success implies the asserted bit is true,
  `ensure_zero_bit` success implies the bit is false, failed `eq_256`
  participant comparisons imply distinct words, the threshold `le_32` asserts
  imply `1 <= threshold <= 3`, and the no-carry `add_32` plus final `le_32`
  minimum-input assertion implies `threshold + prefix <= num_inputs`.
  `ElementsJetEnvironment.v` contains the environment-to-model relation and
  proves that environment-backed current-script-hash, input script-hash,
  input-hash, output-hash, current-index, and `num_inputs` facts discharge the
  corresponding source-block premises.
- `ElementsJetCmr.v` defines the CMR byte constants for the same whitelisted
  Elements jets from the upstream Elements `primitiveJetNode.inc` table. Coq
  checks that each entry is a 32-byte value and a 256-bit CMR bitstring, and the
  module exposes an adapter for plugging those jet CMRs into the byte decoder's
  CMR algebra.
- `CmrWellFormed.v` defines the 256-bit-output contract for executable CMR
  algebras. It proves that, under that contract and decoded hidden-CMR
  well-formedness, the checked CMR pass agrees with the ordinary CMR
  computation. It also proves the Elements jet CMR adapter preserves that
  contract, so the remaining CMR task is the foundation-backed core hash/tag
  algebra rather than the jet table.
- `FoundationCmrAlgebra.v` packages a foundation-shaped CMR adapter interface
  matching the upstream Merkle-root operation shape: commitment tags for nullary
  nodes, `compress_half` for unary nodes, `compress` for binary nodes, and
  explicit word/fail/jet functions. Coq proves this adapter satisfies the local
  256-bit CMR-algebra contract once the operations are supplied. It also exposes
  checked shape lemmas showing that assertion nodes use the case-tag compression
  shape, two-child disconnect uses the disconnect-tag unary shape, and the
  Elements-wrapped algebra uses the audited Elements jet CMR table. This does
  not instantiate SHA256 or tag constants yet; that remains the
  `Simplicity.Digest`/`Simplicity.MerkleRoot` dependency task.
- `ElementsJetTypes.v` defines the source and target types for the same
  whitelisted Elements jets from the upstream Elements `primitiveJetNode.inc`
  and `primitiveInitTy.inc` tables. The theorem
  `elements_jet_typecheck_accepts_declared_arrow` checks that `TypedBridge.v`'s
  jet-node checker accepts those declared arrows.
- `BridgeTypeTranslation.v` defines a Unit/Sum/Prod type-algebra interface and
  proves that any atom-free bridge type table translates into that interface.
  The concrete compiled typed certificate is proved to translate for every such
  algebra.
- `FoundationTypes.v` imports the standalone upstream `Simplicity.Ty` file and
  instantiates that algebra with the actual foundation `Unit`, `Sum`, and
  `Prod` constructors. `CompiledMultisigFoundationTypes.v` contains the
  concrete compiled typed-certificate theorem for those foundation types.
- `FoundationCore.v` exports `FoundationCoreTypes.v`,
  `FoundationCoreTerms.v`, and `FoundationCoreRecursive.v`. Together they
  import standalone upstream `Simplicity.Core` and prove that any checked typed
  structural evidence for a core node form (`iden`,
  `comp`, `unit`, `injl`, `injr`, `case`, `pair`, `take`, or `drop`) can be
  realized as an actual foundation `Term` at the translated foundation arrow,
  assuming its child references already have foundation terms. It also builds
  child-term providers recursively from checked typed prefixes, and packages the
  typed byte root theorem behind only explicit non-core primitive term providers
  for assertions, jets, witnesses, words, and disconnect nodes.
- `FoundationElementsProviders.v` narrows that generic non-core obligation for
  the multisig typed-certificate hook profile: callers supply providers only
  for assertion, Elements jet, witness, word, and two-child disconnect nodes,
  while Coq discharges fail nodes and reserved one-child disconnect nodes from
  the hook rejection proofs.
- `CompiledMultisigFoundation.v` applies the generic typed-byte root theorem to
  the actual generated compact typed multisig certificate. It proves that the
  decoded concrete artifact has an upstream foundation root term once that
  narrowed Elements provider family is supplied. It also exposes the same
  root-term conclusion from checked-CMR compact typed bridge evidence and from a
  successful typed streaming checked-program run, so the stronger
  byte+type+declared-CMR artifact path has a named foundation entry point.
- `CompiledMultisigFoundationCmrEvidence.v` specializes the successful checked
  typed streaming run to `foundation_elements_cmr_algebra ops` and exposes the
  direct byte-decoder facts: the concrete program bytes stream-decode to the
  returned program and the checked CMR computation equals the exported artifact
  CMR under that foundation-shaped adapter.
- `CompiledMultisigFoundationSecurity.v` composes that checked typed+CMR
  foundation entry point with the concrete artifact security theorem. Given the
  narrowed Elements provider family and either explicit dynamic
  prefix/`CountVotes`/threshold-count premises or the stronger semantic package
  of static/prefix/minimum assertion facts plus executed vote slots and the
  final threshold assertion from `ElementsJetEnvironment.v`, Coq derives the
  full model security property while also returning the concrete foundation root
  term for the checked artifact.
- `CompiledMultisigFoundationCmrSecurity.v` specializes the strongest checked
  artifact theorem to `foundation_elements_cmr_algebra ops`, so the top checked
  security statement no longer exposes an arbitrary `CmrAlgebra`. The remaining
  premise is a successful typed streaming checked-program run using a
  `FoundationCmrOps` implementation.
- `SimplicityByteDecoder.v` is a compatibility wrapper around the byte-decoder
  layers: `SimplicityByteDecoderBits.v`, `SimplicityByteDecoderProgramTypes.v`,
  `SimplicityByteDecoderRawOrder.v`, `SimplicityByteDecoderConversionCore.v`,
  `SimplicityByteDecoderConversionProperties.v`,
  `SimplicityByteDecoderValidation.v`, `SimplicityByteDecoderBitParser.v`,
  `SimplicityByteDecoderCursorParser.v`,
  `SimplicityByteDecoderDecodeRawProofs.v`,
  `SimplicityByteDecoderDecodeStructuralCore.v`,
  `SimplicityByteDecoderDecodeStructuralProperties.v`,
  `SimplicityByteDecoderCursorNaturalProofs.v`,
  `SimplicityByteDecoderCursorProgramProofs.v`,
  `SimplicityByteDecoderCmrCore.v`, and
  `SimplicityByteDecoderCmrProofs.v`. Together they start the byte-level
  bridge with an executable Coq decoder for the structural Simplicity program
  encoding. It decodes bytes into raw nodes, rejects natural numbers above the C
  decoder's
  `simplicity_decodeUptoMaxInt` range (`2^31 - 1`), rejects DAG length prefixes
  above the deployed `DAG_LEN_MAX = 8000000` limit, then validates the
  Rust-style hidden-node/assertion rules into a structural program. The raw
  decoder also proves every decoded child reference is a strict backward
  reference to an earlier raw node, matching the positive-offset rule in the C
  decoder. It also checks that the raw nodes are in canonical root-reachable
  postorder and rejects the no-witness fail opcode, matching the deployed
  no-witness DAG decoder's artifact boundary. It now also computes and
  verifies the decoded
  structural program's root CMR under an explicit CMR algebra, with a checked
  path that rejects non-256-bit computed or expected CMRs. `CmrWellFormed.v`
  packages the 256-bit-output obligation, `ElementsJetCmr.v` composes the
  checked Elements jet CMR table, and `FoundationCmrAlgebra.v` gives the
  foundation-shaped adapter surface. The adapter still needs to be instantiated
  with the Simplicity foundation's concrete `CommitmentRoot` hash/tag functions.
  Typed conversion, full
  maximal-sharing checks by semantic node identity, and semantic evaluation
  remain future bridge work. The structural program now exposes its contained
  jets, with a checked theorem that every structural program produced by this
  decoder is restricted to the multisig Elements jet whitelist. It also checks
  a structural DAG invariant: the decoded root is a real node and every child
  reference in every structural node points backward to an already converted
  real node rather than to a hidden placeholder or future node. That invariant
  is also exposed as a Prop-level theorem: any child reference of any decoded
  real node resolves to an earlier decoded real node. Accepted decoded byte
  programs also have checked `structural_program_no_fail`,
  `structural_program_no_disconnect1`,
  `structural_program_hidden_cmrs_unique`, and
  `structural_program_hidden_cmrs_256` theorems, so the no-witness fail
  opcode is absent, the reserved one-child disconnect code is absent, hidden
  CMR payloads are not duplicated, and every hidden CMR payload is exactly
  256 bits. The byte decoder also mirrors the deployed close-bitstream rule:
  after the final
  decoded node it accepts only zero padding shorter than one byte, rejecting
  non-zero padding and full trailing zero bytes.
- `TypedBridge.v` exports `TypedBridgeCore.v` and `TypedBridgeEvidence.v`,
  which add the next checked bridge layer: an exported type table can be
  checked against the decoded structural program. Core combinator typing is
  checked directly, hidden CMR placeholders are required to have no type entry,
  and jets/witnesses/words/fails/disconnects are delegated to explicit hooks.
  The standard Elements hook profile now instantiates Elements jets,
  Simplicity witness admissibility, words, fail rejection, reserved one-child
  disconnect rejection, and the two-child disconnect type rule. Its
  evidence now also proves that the exported table length equals the
  decoded node count, every real node has a `Some` arrow, and every hidden
  placeholder has `None`; combined with byte-DAG evidence, every child reference
  resolves to an earlier real node with a type arrow and the root is a real node
  with the declared root arrow. It also carries the byte decoder's no-fail fact
  and indexed theorems excluding `SFail` and `SDisconnect1` nodes from the
  typed byte artifact.
  The node checker also exposes a Prop-level
  `structural_node_type_evidence` theorem for every accepted node form, and the
  aggregate typed evidence now stores enough proof data to recover that premise
  for any indexed real node. This lets later conversion consume named typing
  premises instead of raw booleans. `ElementsJetTypes.v` now
  instantiates the whitelisted Elements jet source/target hook, Simplicity
  witness admissibility, the word type rule, fail rejection, reserved one-child
  disconnect rejection, and the two-child disconnect type rule. `FoundationCore.v`
  consumes that Prop-level evidence for the pure core node forms and constructs
  upstream `Simplicity.Core.Term` witnesses. It now recursively derives the
  child-term provider for typed prefixes and packages typed byte root
  construction behind explicit non-core primitive providers.
  `FoundationElementsProviders.v` narrows those providers to the allowed
  Elements non-core node families and proves rejected fail/`disconnect1` nodes
  cannot satisfy the typed-certificate hooks. `CompiledMultisigFoundation.v`
  instantiates that theorem for the concrete generated compiled multisig
  artifact, including checked-CMR entry points that consume either concrete
  decoded-program plus declared-CMR equality premises or the direct successful
  typed streaming checker result.
  The jet-level semantic-spec bridge now covers the static participant,
  threshold, prefix/current-index, environment lookup, and minimum-input
  assertions. It also packages those assertion facts together with the
  `ElementsVoteSlotsExecution` relation and final vote-threshold assertion to
  derive `CountVotes`, the threshold-count fact, and then
  `multisig_covenant_succeeds`. Supplying concrete foundation primitive
  providers for assertions, Elements jets, witnesses, words, two-child
  disconnects, plus deriving that execution relation from full
  hash/Taproot/signature semantic evaluation, remains future
  primitive/foundation bridge work.
- `crates/contracts/src/multisig/builder.rs` now exports a
  `CompiledMultisigCertificate` containing the compiled no-witness program
  bytes, CMR, root arrow, and per-node type table from the same `CommitNode`,
  plus a stable JSON artifact form and generated Coq modules containing the
  same certificate as constants. The default `coq` module is the lean
  byte-certificate artifact imported by the formal audit. The separate
  `coq-typed` module emits a compact indexed typed certificate:
  type definitions, arrow definitions, per-node arrow indexes, and a root-arrow
  index. `coq-typed-split <output_dir>` emits the same byte and typed
  certificate as the smaller `CompiledMultisigTypedExample*.v` module family
  used by this formal tree. Coq expands that compact artifact with
  `expand_compact_typed_certificate`, then the generated decode-only typed
  checker theorem packages typed evidence whenever the compact table checks
  against the streamed decoded bytes. The
  generated Coq module also defines `compiled_multisig_decoded_program` by
  applying the decode-only certificate checker to those bytes. It now also
  defines `compiled_multisig_streaming_decoded_program` using the streaming
  certificate checker and proves
  `compiled_multisig_streaming_decode_evidence`, an existential theorem that
  packages the actual compiled bytes as
  `CompiledMultisigByteCertificateStreamingDecodeEvidence`, including the raw
  byte-decoder result, the strict raw-backreference proof, the canonical
  root-reachable order proof, and hidden-CMR uniqueness/256-bit-length proofs
  behind the structural program. It also defines
  `compiled_multisig_streaming_checked_program` and proves the conditional
  theorem `compiled_multisig_streaming_bridge_evidence_if_checked_cmr`, which
  packages checked CMR equality to the exported CMR whenever a supplied concrete
  CMR algebra accepts the streamed bytes.
  `CompiledMultisigExample.v` is one concrete generated artifact that is
  imported by the formal build. It proves that the concrete program bytes are
  accepted by the streaming Coq raw-DAG byte decoder and structurally validate
  to some `StructuralProgram`, using a streaming parser and a linear
  root-reachability check rather than eagerly expanding the whole byte list into
  bits. The Rust round-trip test
  verifies those bytes
  decode back to the same CMR and re-encode canonically. The certificate can be
  regenerated with
  `cargo run -p simplicity-native-multisig-contracts --example export_multisig_certificate -- <json|coq|coq-typed> <threshold> <participant1_xonly_hex> <participant2_xonly_hex> <participant3_xonly_hex>`.
  Use `coq-typed-split <output_dir>` before the threshold to regenerate the
  split checked-in Coq module family.
  The generated streaming-success theorem is connected to an aggregate
  certificate evidence theorem, and the streaming checked-CMR path has a
  conditional bridge-evidence theorem. The concrete artifact also exposes
  `compiled_multisig_threshold` and the three decoded participant keys, proves
  their static threshold/distinctness checks, and composes those static facts
  with explicit prefix and `CountVotes` premises into both
  `multisig_source_blocks_succeed` and `multisig_covenant_succeeds` for the
  concrete declared participant set. It then composes the concrete model
  success theorem with the model security theorem to prove that, under those
  same dynamic premises, the compiled artifact authorizes at least
  `compiled_multisig_threshold` distinct declared participants and satisfies
  the full model security property. `MultisigCertificate.v` also packages a
  bridge theorem from decode evidence plus ordinary CMR equality under a
  `CmrWellFormed.v` algebra. `CompiledMultisigFoundationCmrEvidence.v` exposes
  the decoded-program and checked-CMR projections for that path specialized to
  the foundation-shaped adapter, and `CompiledMultisigFoundationCmrSecurity.v`
  specializes the strongest checked security theorem to the same adapter. The
  remaining byte-level CMR task is instantiating `FoundationCmrOps` from the
  Simplicity foundation and proving that the checked run accepts the deployed
  artifact's exported CMR.
- `MultisigCertificate.v` exports the byte-certificate modules:
  `MultisigCertificateCore.v` for the artifact shape and low-level checkers,
  `MultisigCertificateShape.v` for shape/static-field facts,
  `MultisigCertificateChecks.v` for checked decoder entry points,
  `MultisigCertificateProperties.v` for inherited decoder properties,
  `MultisigCertificateEvidence.v` for aggregate bridge evidence, and
  `MultisigCertificateExamples.v` for generated-artifact examples. The
  decode-only checker validates byte ranges, participant/CMR lengths, threshold
  bounds, and then invokes the checked Simplicity byte decoder. Its full checker
  additionally invokes the checked CMR verifier. Its soundness
  lemmas now expose both sides needed by later bridge proofs: accepted
  certificates decode to a structural program with the expected checked CMR, and
  their static fields satisfy the model-level threshold and participant-count
  bounds. Accepted certificates also inherit the decoder's jet-whitelist and
  structural DAG well-formedness theorems, including the Prop-level
  child-reference theorem needed by typed conversion, and the no-fail plus
  no-`disconnect1` theorems required by the no-witness artifact format. It also
  exposes the structural
  node-count bound inherited from `DAG_LEN_MAX`, the closed-padding theorem
  for the exported program bytes, the raw byte-decoder result with its strict
  raw-backreference and canonical root-reachable order proofs, plus the `NoDup`
  and 256-bit-length proofs for hidden CMR payloads. It now also proves that
  decode evidence plus ordinary CMR equality under a well-formed CMR algebra is
  enough to construct the existing checked CMR bridge evidence, including the
  typed streaming bridge evidence when a type-table proof is already available.
  The aggregate theorem
  `check_compiled_multisig_byte_certificate_bridge_evidence` packages these
  facts as the byte-level bridge contract that later typed conversion and
  semantic refinement proofs should consume. The typed aggregate theorem
  `check_compiled_multisig_byte_certificate_typed_bridge_evidence` composes
  this byte-certificate evidence with `TypedBridge.v`'s checked type-table
  evidence.
- `MultisigTypedCertificate.v` exports
  `MultisigTypedCertificateCore.v`, `MultisigTypedCertificateEvidence.v`, and
  `MultisigTypedCertificateExamples.v` for the first-class typed
  byte-certificate checker. It can check an exported per-node type table and
  expected root arrow against either the streaming decode-only byte certificate
  or the streaming CMR-checked byte certificate, using `ElementsJetTypes.v` for
  the whitelisted Elements jet arrows. The checker and evidence theorems are
  audited, including
  indexed per-node Prop typing,
  type-table length, node-shape, typed-child-reference, real-root-arrow checks,
  indexed no-fail-node exclusion, and indexed no-`disconnect1` exclusion. The
  Rust exporter now emits the concrete typed artifact compactly through
  `coq-typed`, and the audited compact checker expands it before invoking the
  typed bridge. `CompiledMultisigTypedExample.v` imports the audited byte
  example and the split generated data modules
  `CompiledMultisigTypedExampleTypeDefs.v`,
  `CompiledMultisigTypedExampleArrowDefs*.v`,
  `CompiledMultisigTypedExampleTypeTable*.v`, and
  `CompiledMultisigTypedExampleData.v`. It checks that the concrete compact
  type artifact expands, proves that the compact type definitions and expanded
  typed certificate contain no `BTAtom` escape-hatch types, proves the expanded
  certificate translates into any Unit/Sum/Prod type algebra, proves
  `compiled_multisig_streaming_typed_decoded_program = Some program` for the
  concrete artifact, and packages that result as concrete compact
  decode-only typed evidence. It also exposes a direct checked typed program
  definition and theorem, plus named projections showing that any successful
  direct checked run decoded the concrete certificate bytes and recomputed the
  exported CMR through the checked CMR path. Composition theorems can also
  consume existing byte-decode evidence, a type-table check, and ordinary CMR
  equality under a well-formed CMR algebra, avoiding another byte-decoder run
  while constructing compact typed checked-CMR bridge evidence.
  `CompiledMultisigFoundation.v` consumes that checked-CMR bridge evidence to
  produce the same conditional upstream foundation root term, and now also
  accepts the direct successful typed streaming checked-program result. Both
  entry points are phrased against the narrower Elements provider family.
  `CompiledMultisigFoundationSecurity.v` composes the checked typed+CMR
  foundation-term path with the concrete artifact security theorem, including
  the direct successful checked-program entry point, under either the
  still-explicit dynamic vote premises or the stronger `ElementsJetEnvironment.v`
  package of static/prefix/minimum assertion success, executed vote slots, and
  the final threshold assertion. Witness value semantics plus concrete primitive
  providers for those node families are still open.
- `MultisigSourceBlocks.v` contains source-level SIMF block lemmas, starting
  with the proof that the three participant inequality checks imply
  `NoDup [participant1; participant2; participant3]`. It also combines the
  threshold and participant checks into the static model facts required by
  `multisig_covenant_succeeds`: participant count, participant uniqueness, and
  threshold bounds. It now packages the static checks, multisig input-prefix
  checks, input availability check, and vote-counting block into
  `multisig_source_blocks_imply_model_success`, whose conclusion is the actual
  model predicate `multisig_covenant_succeeds`.
- `ElementsJetEnvironment.v` composes the semantic-side static/prefix/minimum
  input assertion bridge with vote-slot execution evidence. The theorem
  `static_prefix_minimum_and_executed_votes_imply_model_success` derives the
  model predicate from static/prefix/minimum assertion success, an
  `ElementsVoteSlotsExecution` trace, and the final threshold assertion. The
  remaining open work is deriving those semantic assertion and execution facts
  from concrete foundation evaluation of the decoded compiled term.

Build:

```sh
cd formal
make
```

Proof-integrity audit:

```sh
cd formal
make audit
```

On hosts without a system Coq installation, this proof was checked with:

```sh
nix-shell --pure -p rocq-core rocqPackages.stdlib gnumake findutils coreutils --run 'cd formal && make audit'
```
