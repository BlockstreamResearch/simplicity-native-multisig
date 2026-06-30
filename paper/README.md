# LaTeX Paper Draft

This directory contains the working skeleton for a future paper about the
Simplicity native multisig protocol implemented in this repository.

Start with `main.tex`. It contains the current dictated paper draft.

## Build

```bash
make
```

The `Makefile` uses XeLaTeX through `latexmk`:

```bash
latexmk -xelatex -outdir=out -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

The generated PDF is written to `out/main.pdf`.

Use `make clean` to remove intermediate files and `make distclean` to remove
all generated LaTeX outputs, including the `out/` directory.

## Style Basis

This is a portable cryptography preprint-style template. It is not locked to a
single publication venue yet.

Primary sources checked:

- [IACR ePrint operations](https://eprint.iacr.org/operations.html): acceptance
  criteria expect cryptology submissions to be clear, readable,
  self-contained, and to contain proofs or convincing arguments for claims.
- [IACR LaTeX repository](https://github.com/IACR/latex): IACR maintains
  official LaTeX classes for IACR journal publications, including `iacrj.cls`.
- [Springer LNCS author information](https://link.springer.com/series/558/information-for-authors-and-editors):
  Springer provides official proceedings author instructions and a LaTeX
  proceedings template, which is still common for conference proceedings.

Template implications:

- Keep the paper self-contained.
- Separate preliminaries, system model, construction, correctness, security
  definitions, security analysis/proofs, implementation, and evaluation.
- Use theorem, definition, experiment, construction, and proof environments for
  cryptographic claims.
- Migrate to `iacrj` or LNCS only after the target venue is known.

Useful source anchors while writing:

- `../crates/contracts/simf/multisig_n_of_3.simf`
- `../crates/contracts/simf/vote.simf`
- `../crates/contracts/src/multisig/builder.rs`
- `../crates/contracts/src/vote/builder.rs`
- `../crates/contracts/src/vote/message.rs`
- `../crates/contracts/tests/regtest/`
