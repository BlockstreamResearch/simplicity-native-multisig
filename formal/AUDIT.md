# Proof integrity audit

This audit checks that the Rocq artifact is a legitimate proof of the stated
theorems and does not rely on hidden proof shortcuts.

## Commands

```sh
cd formal
make clean
make audit
```

On hosts without a system installation:

```sh
nix-shell --pure -p rocq-core rocqPackages.stdlib gnumake findutils coreutils \
  --run 'cd formal && make clean && make audit'
```

The full audit rebuilds every module serially, then runs the two verification
phases below. Expect ~35 minutes wall time with peak memory under ~1.2 GB.
Never build this tree with `make -j` (see the proof-style notes in
`README.md`).

## What the audit verifies

1. **No proof shortcuts.** The proof source contains no `Axiom`, `Parameter`,
   `Admitted`, `admit`, `Abort`, `Conjecture`, `vm_cast_no_check`, or
   `native_cast_no_check`. Abstract cryptographic and chain primitives are
   section variables, not global axioms: after each section closes, theorem
   statements quantify over those primitives explicitly.
2. **Closed assumptions for every named theorem.** The `audit` target runs
   `Print Assumptions` on every named theorem across all layers — the model
   security theorems, the source-block bridges, the byte decoder and typed
   checker soundness/evidence theorems, the CMR algebra and jet-table
   theorems, the foundation adapters, the concrete-artifact discharge
   theorems (decode, type check, real SHA-256 CMR, checked run), the
   real-algebra security instantiations, and the deployed-bytes execution
   theorems. Every one must report:

   ```text
   Closed under the global context
   ```

   As of 2026-07-03 that is 324 checks, all closed. The theorem list lives in
   the `audit` target of the `Makefile`; any newly added theorem should be
   appended there.
3. **Independent kernel verification.** `rocqchk` re-checks every compiled
   module (including the vendored copies of upstream `Simplicity.Ty` and
   `Simplicity.Core`) with the standalone kernel checker — this re-runs the
   closed computations, including the real-CMR recomputation and the five
   deployed-program executions — and must print:

   ```text
   rocqchk: OK
   ```

## Boundary

What the audited theorems cover, and what they do not, is stated precisely in
`README.md` ("What is machine-checked" and "Trust boundaries"). In one line:
the model security property, the source-block bridge, the exporter-trust-free
identity of the deployed artifact (decode + types + byte-exact SHA-256 CMR),
the discharged checked run with the security theorems instantiated on it, and
the concrete accept/reject execution behavior of the deployed bytes are all
proven axiom-free; the universal execution-refinement theorem (evaluation
success implies the vote-execution premises for arbitrary environments) is
the remaining open obligation, documented in `FOUNDATION_PLAN.md` and
`GENERALIZATION.md`.
