# Bridge theorem targets and obligations

> **Status (2026-07-03).** Kept as design history; most targets below are now
> achieved and audited. The compiled program IS a Coq object: the deployed
> bytes decode, type-check, and CMR-match byte-for-byte under a
> self-contained FIPS-proven SHA-256 (`CompiledMultisigRealCmr.v`), the full
> checked run is discharged and the strongest security theorems are
> instantiated on it (`CompiledMultisigRealSecurity.v`), and the deployed
> bytes execute inside Coq with proven accept/reject behavior on concrete
> scenarios (`CompiledMultisigExecution.v`). The one remaining obligation
> from this document is the universal semantic-refinement theorem: successful
> evaluation implies the assertion/vote-execution premises for arbitrary
> environments and witnesses. Current state: `README.md`.

## What the compiled opcodes do not give by themselves

Compiled bytes prove only that a Rust compiler produced a byte encoding. They
do not, by themselves, prove the high-level security statement.

The missing pieces are:

1. A Coq representation of the exact compiled program, or a verified decoder
   from the byte encoding into such a representation. This is now partially
   implemented for the concrete artifact: the Rust-side
   `CompiledMultisigCertificate` provides the byte string and CMR, and Coq's
   streaming decoder validates the structural DAG, child references, padding,
   hidden CMR shape, no-fail/no-`disconnect1` restrictions, and multisig jet
   whitelist for those bytes. The remaining part is semantic execution of that
   decoded typed program, not merely importing the bytes.
2. A concrete CMR instantiation that matches the Simplicity foundation's
   `CommitmentRoot` hash/tag functions and Rust's `Cmr` implementation. The
   Elements jet CMR half of this table is now present in `ElementsJetCmr.v`.
   `CmrWellFormed.v` proves the 256-bit-output contract needed to turn ordinary
   CMR computation into the checked-CMR decoder path, and proves the Elements
   jet adapter preserves that contract. `FoundationCmrAlgebra.v` now packages
   the foundation-shaped tag/`compress_half`/`compress` adapter surface and
   proves it satisfies the local checked-CMR contract once concrete operations
   are supplied. The remaining CMR gap is instantiating that surface from
   upstream `Simplicity.Digest`/`Simplicity.MerkleRoot` and resolving the Coq
   version/dependency setup needed to import those modules.
3. A default-audit path for checking the exported compact concrete type-table
   artifact in Coq, a theorem tying
   `ElementsJetTypes.v`'s `BridgeType` representation to the foundation's
   `Simplicity.Ty`, and a conversion theorem from the typed structural program
   to a foundation `Term`. The Rust exporter can already emit the concrete type
   artifact compactly through `coq-typed`, and Coq has audited compact
   expansion/evidence checkers. The default audit now imports a type-only
   concrete compact typed example, checks that the compact artifact expands,
   proves that the compact typed decoder succeeds for the concrete artifact,
   and packages the result as compact typed decode evidence.
4. Coq semantics for every non-core node used by the program: assertions,
   witnesses, jets, pruning behavior where relevant, and Elements environment
   access.
5. Coq specifications for the Elements jets used by the multisig:
   `current_script_hash`, `input_script_hash`, `input_hash`, `output_hash`,
   `num_inputs`, `current_index`, SHA256 context jets, Taproot construction
   jets, `bip_0340_verify`, equality, padding, arithmetic, and comparisons.
6. ABI decoding lemmas tying Rust/SimplicityHL parameters and witness values to
   the Coq values used in `MultisigSecurity.v`.
7. A semantic proof that successful evaluation of the compiled program implies
   the model predicate `multisig_covenant_succeeds`.

The compiled opcodes are therefore an input to the bridge. They are not the
bridge.

## Creating the byte artifact

The current Rust bridge surface has a repeatable artifact command:

```sh
cargo run -p simplicity-native-multisig-contracts \
  --example export_multisig_certificate -- \
  coq 2 \
  <participant1_xonly_hex> \
  <participant2_xonly_hex> \
  <participant3_xonly_hex>
```

The same command accepts `json` instead of `coq`; use
`coq-typed-split <output_dir>` to regenerate the split typed Coq module
family. The JSON artifact is useful for external tooling. The exporter emits
data only (never proof text); the `coq` format prints the byte-certificate
data module (`CompiledMultisigByteData.v`), which in the formal tree defines:

```coq
compiled_multisig_certificate : CompiledMultisigByteCertificate
compiled_multisig_decoded_program :=
  check_compiled_multisig_byte_certificate_without_cmr
    compiled_multisig_certificate
compiled_multisig_streaming_decoded_program :=
  check_compiled_multisig_byte_certificate_streaming_without_cmr
    compiled_multisig_certificate
compiled_multisig_streaming_checked_program alg :=
  check_compiled_multisig_byte_certificate_streaming
    alg compiled_multisig_certificate
```

That generated module is intentionally not the final theorem. It lets Coq check
that the exported threshold, participant keys, program bytes, and CMR bytes can
be imported as constants, and it exposes the exact decoder expression that must
be discharged for this artifact. `formal/CompiledMultisigExample.v` is one
concrete generated instance imported by the formal build; it proves that any
`Some program` result from the decode-only checker carries
`CompiledMultisigByteCertificateDecodeEvidence`. The generated artifact also
proves that the concrete bytes are accepted by a streaming Coq raw-DAG decoder,
have canonical root-reachable order, and structurally validate to some
`StructuralProgram`. This avoids the eager
`bytes_to_bits` expansion that made even length-prefix checks impractical under
`vm_compute`, and replaces the previous DFS-style canonical-order check with a
linear root-reachability check. That streaming result is now connected to the
aggregate certificate evidence theorem through
`compiled_multisig_streaming_decode_evidence`, so later bridge layers consume a
proof record rather than a bare decoder equality. The generated module also
contains `compiled_multisig_streaming_bridge_evidence_if_checked_cmr`, which
turns any successful streaming checked-CMR run into
`CompiledMultisigByteCertificateStreamingBridgeEvidence`. The certificate layer
also has theorems that turn streaming decode evidence plus ordinary CMR
equality into the same checked bridge evidence, including typed evidence when
a type-table proof is already available, provided the CMR algebra satisfies
`CmrWellFormed.v`. `CompiledMultisigFoundationCmrSecurity.v` also specializes
the strongest checked-artifact security theorem to the foundation-shaped CMR
adapter, so the top theorem no longer exposes an arbitrary `CmrAlgebra`. The
remaining CMR work is not the checker interface; it is instantiating
`FoundationCmrOps` from the Simplicity foundation, proving the concrete checked
run accepts the deployed artifact's exported CMR, and keeping that instantiation
aligned with Rust's CMR implementation.
The concrete module also exposes the artifact's decoded threshold and three
participant keys, proves the static source checks for those values, and proves
that explicit prefix, `CountVotes`, and threshold-count premises imply both
source-block success and `multisig_covenant_succeeds` for the concrete declared
participant set. It also composes that concrete model-success theorem with the
existing model security theorem, so those same dynamic premises imply
threshold-distinct-declared-participant authorization and the full model
security property for the concrete artifact. The strongest semantic bridge now
also derives those dynamic vote premises from `ElementsVoteSlotsExecution` plus
the final threshold assertion, after the static/prefix/minimum assertion facts
are supplied.

A typed artifact adds the concrete per-node type table and expected root arrow,
encoded compactly as type, arrow, table-entry, and root-arrow indexes. It then
calls either the streaming decode-only compact typed checker or the streaming
CMR-checked compact typed checker. Those checkers exist in Coq, and the Rust
exporter now emits the compact real type artifact plus compact evidence
theorems through the `coq-typed` format. The checker proves the table length
and real/hidden node-entry shape, and composes it with byte child-reference/root
evidence so children and the root have typed arrows. It also exposes indexed
Prop-level typing premises for accepted node forms plus indexed no-fail-node
and no-`disconnect1` evidence. The default audit imports a type-only concrete
compact typed example, checks that the compact artifact expands, proves that
the concrete compact typed checker returns `Some program`, and packages that as
compact typed decode evidence. The audited bridge also has composition
theorems that take existing byte-decode evidence, a type-table check, and
ordinary CMR equality under a well-formed CMR algebra to produce compact typed
checked-CMR bridge evidence without re-running the byte decoder.
The checked path now also has named projections from compact typed checked-CMR
evidence back to byte bridge evidence, decoded-byte equality, and checked CMR
equality; the concrete compiled artifact instantiates those projections for
`compiled_multisig_streaming_typed_checked_program`.
`CompiledMultisigFoundationCmrEvidence.v` specializes the direct decoded-program
and checked-CMR projections to `foundation_elements_cmr_algebra ops`, which is
the entry point the concrete `FoundationCmrOps` implementation must satisfy.
It also proves that the concrete compact typed artifact expands to a type table
and root arrow containing no `BTAtom` constructors, and the checked adapter now
translates that table into upstream `Simplicity.Ty`. The checked core adapter
now covers construction of upstream `Simplicity.Core.Term` for pure core node
forms and recursively composes typed-prefix child terms up to a typed-byte root
when non-core primitive providers are supplied. `FoundationElementsProviders.v`
narrows the provider surface to the non-core node families accepted by the
multisig typed-certificate hooks. That result is instantiated for the concrete
compiled multisig typed artifact in `CompiledMultisigFoundation.v`, including
the checked-CMR compact typed bridge evidence path and variants that consume the
narrowed Elements provider family. `CompiledMultisigFoundationSecurity.v`
composes that checked typed+CMR root-term path with the concrete artifact
security theorem under explicit dynamic prefix, `CountVotes`, and
threshold-count premises, and also under the semantic static/prefix/minimum
assertion-success package plus executed vote slots and the final threshold
assertion from `ElementsJetEnvironment.v`. The strongest variants now consume a
successful typed streaming checked-program result directly, instead of separate
decoded-program and unchecked-CMR premises, and the CMR-specialized variant
requires that successful run under `foundation_elements_cmr_algebra ops`. The
remaining implementation work is to instantiate `FoundationCmrOps` from the
foundation/Rust-compatible CMR functions, implement the providers across
assertions, jets, witnesses, words, and two-child disconnect nodes, connect
witness values during semantic evaluation, and prove that successful foundation
execution produces those assertion and executed-vote facts.

## Target theorem

The bridge theorem should have this shape:

```coq
Theorem compiled_multisig_implies_model_success :
  forall env tx current_script_hash total_proposed_outputs
         threshold current_index participants votes,
    eval_elements compiled_multisig env witness = Some tt ->
    decode_elements_env env =
      Some (tx, current_index, current_script_hash) ->
    decode_multisig_parameters compiled_multisig =
      Some (threshold, participants) ->
    decode_multisig_witness witness =
      Some (votes, total_proposed_outputs) ->
    multisig_covenant_succeeds
      tx
      current_script_hash
      total_proposed_outputs
      threshold
      current_index
      participants
      votes.
```

The exact names will change once the Elements primitive module exists. The
important part is the direction: concrete success implies the abstract model
predicate already proved secure.

The final theorem then composes:

```coq
compiled_multisig_implies_model_success
  + multisig_success_security_property
  = compiled success authorizes at least threshold distinct declared participants
```

## Multisig-specific proof obligations

For this covenant, the bridge needs one lemma per meaningful SIMF block:

- `ensure_distinct_participants`:
  three failed `eq_256` comparisons imply `NoDup participants`. This is now
  proved for the three participant slots, both at the source-block level and
  from the jet-level `ensure_zero_bit (eq_256 ...)` semantic spec.
- Threshold validation:
  the concrete asserts imply `1 <= threshold <= 3`. This is now proved and
  composed with participant distinctness into the static model-field theorem;
  the jet-level `verify (le_32 ...)` semantic spec now discharges the source
  threshold premise.
- `base_message_and_input_count`:
  scanning inputs with `current_script_hash` counts exactly the prefix of
  multisig inputs and hashes the corresponding `input_hash` values.
- Proposed-output hashing:
  the output loop hashes exactly the first `TOTAL_PROPOSED_OUTPUTS` output
  hashes used in the model base message.
- `minimum_inputs_num` assert:
  no-carry `add_32 threshold prefix` plus the final `le_32` assertion imply
  `threshold + prefix <= num_inputs`; `ElementsEnvTxRelation` now connects the
  Elements environment's `num_inputs` value to the model transaction input list
  length.
- `verify_vote_input`:
  the vote input's script hash equals the Taproot commitment built from the
  vote executable leaf hash and signature. This is now represented in the
  semantic execution relation as `vote_input_script_hash_assert_succeeds`.
- `checksig`:
  `bip_0340_verify` succeeds for the participant key and
  `SHA256(vote_executable_leaf_hash || base_message)`. This is now a premise of
  the executed-vote case in `ElementsVoteSlotsExecution`.
- `count_vote_entry` and `count_votes`:
  counted slots correspond to declared participants in declaration order, and
  absent vote slots are not counted. This is now captured by
  `ElementsVoteSlotsExecution` and proved to imply `CountVotes`.
- Final threshold assert:
  the counted vote list length is at least `threshold`. The semantic
  `vote_threshold_assert_succeeds` theorem now turns the final `le_32`
  assertion into the model threshold-count fact.

These obligations are exactly what collapse the low-level Simplicity execution
into the abstract predicate in `MultisigSecurity.v`.
