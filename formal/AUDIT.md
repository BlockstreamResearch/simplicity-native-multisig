# Proof integrity audit

This audit checks that the Coq artifact is a legitimate proof of the stated
covenant-model theorem and does not rely on hidden proof shortcuts.

## Commands

```sh
cd formal
make clean
make audit
```

On hosts without a system Coq installation:

```sh
nix-shell --pure -p rocq-core rocqPackages.stdlib gnumake findutils coreutils --run 'cd formal && make clean && make audit'
```

## Shortcut checks

The proof source contains no `Axiom`, `Parameter`, `Admitted`, `admit`, `Abort`,
`Conjecture`, `vm_cast_no_check`, or `native_cast_no_check`.

The abstract cryptographic and chain primitives are section variables, not
global axioms. After the section closes, theorem statements quantify over those
primitives explicitly.

`Print Assumptions multisig_success_security_property` reports:

```text
Closed under the global context
```

`Print Assumptions multisig_success_authorizes_threshold_distinct_declared_participants`
also reports:

```text
Closed under the global context
```

The bridge checker theorems audited by `make audit` also report:

```text
Closed under the global context
```

This includes the Elements jet decoder roundtrip theorem, Elements jet whitelist
theorems, Elements jet semantic assertion-to-source-block bridge theorems,
the semantic assertion plus counted-vote bridge to
`multisig_covenant_succeeds`, Elements environment-to-transaction-list bridge theorems,
Elements jet CMR byte-range and 256-bit length theorems, Elements jet
source/target, witness-admissibility, word, fail-rejection, reserved one-child
disconnect rejection, and disconnect type-hook theorems,
structural byte decoder validation, DAG
well-formedness, and
Prop-level child-reference theorems, the no-witness no-fail byte-decoder
and no-`disconnect1` byte-decoder theorems, positive-natural max-int and DAG
length-bound theorems,
strict-backreference theorems, raw-program/canonical-order extraction theorems,
streaming cursor strict-backreference theorems, hidden-CMR uniqueness and
256-bit length theorems, close-bitstream padding theorems, checked CMR
length/equality soundness
theorems for both bit-list and streaming decoders, the CMR-algebra
well-formedness and checked/unchecked CMR agreement theorems, the Elements jet
CMR adapter well-formedness theorem, the
indexed structural no-fail-node and no-`disconnect1`-node theorems, the
compiled byte-certificate checker soundness theorem, the decode-only and
streaming compiled byte-certificate checker and evidence theorems, the
certificate byte-to-bit length and byte/typed/compact-typed
decode-plus-ordinary-CMR bridge composition theorems, the
certificate static-field, raw-program/backreference/canonical-order,
jet-whitelist, DAG well-formedness, DAG length-bound, child-reference, no-fail,
hidden-CMR-uniqueness, hidden-CMR-256-bit-length, and closed-padding soundness
theorems, the concrete
compiled streaming decode evidence theorem, the conditional compiled streaming
checked-CMR bridge theorem, the concrete compiled artifact theorem that its
decoded static threshold and three participant keys satisfy the source static
checks, the concrete compiled artifact composition from explicit prefix and
`CountVotes` premises to source-block success and to
`multisig_covenant_succeeds`, plus the concrete compiled artifact composition
from those same premises to threshold-distinct-declared-participant
authorization and the full model security property, the checked typed+CMR
foundation-artifact composition that returns the concrete foundation root term
and the full model security property under those same dynamic premises, the
aggregate byte-certificate bridge evidence
theorem, the typed structural checker soundness theorem, recursive and indexed
per-node Prop typing soundness theorems, typed table
length/real-hidden-shape, typed-child-reference, and real-root-arrow theorems,
typed no-fail evidence, the typed byte evidence theorem, the typed compiled
byte-certificate bridge theorem, the typed
byte-certificate streaming checker soundness and evidence theorems, compact
type-artifact atom-freeness preservation theorems, the concrete expanded typed
certificate atom-freeness theorem, the generic Unit/Sum/Prod type-algebra
translation theorems, the concrete typed-certificate translation theorem, the
upstream `Simplicity.Ty` adapter theorem, the upstream `Simplicity.Core` core
node `Term` adapter theorem, the conditional typed-byte node/root foundation
term composition theorems, the recursive typed-prefix child-term provider and
typed-byte root theorem that no longer takes caller-supplied child terms, the
checked Elements-provider narrowing theorem that discharges fail and reserved
`disconnect1` forms from the typed-certificate hooks, the concrete compiled
multisig root-foundation theorems conditional on explicit non-core primitive
providers or the narrowed Elements provider family, including the checked-CMR
bridge evidence entry point, direct checked typed program entry point, and
decoded-byte/checked-CMR projections from that direct entry point, and the
source-block theorems that the
three participant inequality checks imply
`NoDup [participant1; participant2; participant3]` and that the static SIMF
threshold/participant checks imply the model's static premises, plus the
source-block composition theorem whose conclusion is
`multisig_covenant_succeeds`.

The `make audit` target also runs `rocqchk` over generated local copies of
upstream `Simplicity.Ty` and `Simplicity.Core` plus all formal modules and
prints:

```text
rocqchk: OK
```

## Boundary

This is a no-hidden-axioms proof for the covenant model in
`MultisigSecurity.v`, plus no-hidden-axioms bridge checker lemmas for the
current byte decoder, typed structural checker, certificate checker, and
source-block artifacts, including the typed byte-certificate checker, the
checked CMR constants for the whitelisted Elements jets, the CMR-algebra
well-formedness layer, and the checked source/target type hooks for those jets
plus Simplicity word nodes, fail rejection, and two-child disconnect typing. The concrete generated example
imported by the default audit is the lean byte-level certificate. The default
audit also imports a type-only concrete compact typed certificate example that
reuses the byte-level certificate, checks that the compact type artifact
expands, proves
`compiled_multisig_streaming_typed_decoded_program = Some program`, and packages
that result as compact decode-only typed evidence. It also proves that the
expanded concrete typed certificate contains no `BTAtom` bridge types, leaving
a total Unit/Sum/Prod shape. It also
audits the generic theorem that such atom-free type tables translate into any
Unit/Sum/Prod type algebra, plus the concrete compiled typed certificate's
translation theorem. `FoundationTypes.v` imports the upstream standalone
`Simplicity.Ty` file and audits the concrete compiled typed certificate's
translation into the actual foundation type constructors. `FoundationCore.v`
imports the standalone upstream `Simplicity.Core` file and audits the theorem
that checked typed evidence for a pure core node form yields an actual
foundation `Term` when its children already have foundation terms. It also
audits recursive typed-prefix child-term construction and a typed-byte root
foundation-term theorem whose remaining non-core primitive node families are
explicit provider obligations rather than hidden assumptions.
`FoundationElementsProviders.v` narrows those obligations to assertion,
Elements jet, witness, word, and two-child disconnect providers and proves fail
and `disconnect1` cannot satisfy the typed-certificate hooks. The audit also
imports `CompiledMultisigFoundation.v`, which applies that theorem to the actual
generated compact typed multisig artifact and to the checked-CMR compact typed
bridge evidence path, including variants that consume the narrowed Elements
provider family. `CompiledMultisigFoundationSecurity.v` is audited separately;
it composes the checked typed+CMR foundation entry point with the concrete
artifact security property under explicit dynamic vote premises and under the
semantic static/prefix/minimum assertion-success package. It also
audits composition theorems that turn existing byte-decode evidence, a
type-table check, and
ordinary CMR equality under a well-formed CMR algebra into compact typed
checked-CMR bridge evidence without re-running the byte decoder.
The Rust exporter can emit the corresponding standalone compact typed module,
and Rust tests check that export boundary.

It is not yet an end-to-end proof that the generated Simplicity/SIMF program
implements `multisig_covenant_succeeds`; that bridge is the explicit next proof
obligation documented in `FOUNDATION_PLAN.md` and `BRIDGE_RESEARCH.md`.
