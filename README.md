# OpenAI #086 — Whole Lean 4 project (core + Lemma 3.3)

**Full SOURCE project, but PARTIAL formalization of the mathematics.**

This is a single download containing **all Lean source files** from our prior
independent project together with the reviewed Lemma 3.3 candidate, Lake
configuration, checks, documentation, and GitHub Actions workflows. It deals
**only** with *An L³ Bound for the Trilinear Hilbert Transform* (OpenAI #086,
5 October 2026), fixed slopes `(1,2,3)`. No Hartley extension is included.

## What is included

- `OpenAI086.lean`: all previously developed core proof components.
- `OpenAI086/Lemma33Reviewed.lean`: candidate dyadic logarithmic estimate for
  noncommuting nested projections (adapted, see `PROVENANCE.md`).
- `OpenAI086/Lemma33Check.lean`: extra `#check` and `#print axioms` commands.
- **`OpenAI086Whole.lean`**: single **FULL** entrypoint importing core AND
  candidate, ensuring the candidate cannot be omitted from a full build.
- `OpenAI086/PaperStatement.lean`: mathematical target Theorem 1.1, currently
  a `def ... : Prop`, with **no proof**. This is deliberately honest.
- `tools/`: structural, symbolic and numerical sanity checks (NOT Lean proofs).
- `.github/workflows/`: CI for the Lean project.
- `PROOF_TRACEABILITY.md`, `LEMMA33_STATUS.md`: proof-coverage reports.

## Setup and test on Ubuntu / WSL

Prerequisite: install `elan` (Lean version manager), Git, Python 3,
and the Python packages `sympy` and `numpy`. Internet is needed for Lean
and Mathlib on the first setup. `lean-toolchain` pins the compiler and
`lakefile.toml` pins the Mathlib revision.

```bash
unzip OpenAI086_Whole_Project.zip
cd OpenAI086_Whole_Project
python3 -m pip install sympy numpy
bash verify_all.sh
```

Or only the standard Lean build:

```bash
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
```

The `verify.sh` script is an alias of `verify_all.sh` (full project).
The `verify_core.sh` script checks just the independently developed core
if you need to isolate compiler errors in the candidate.

## Honest status

| Target | Status before running on your machine |
|---|---|
| Core algebraic and finite-combinatorial Lean declarations | Written; kernel compilation not verified here |
| Lemma 3.3 noncommuting logarithmic bounds | Complete candidate script; kernel compilation not verified here; common row codomain only |
| Lemma 3.4 compression | Not formalized |
| Quantitative Sections 4–9 | Not formalized completely |
| Proposition 2.3 / Theorem 2.2 | Not formalized |
| Theorem 1.1 (Schwartz and L³ extension) | **Not proved** |

Even if `lake build OpenAI086Whole` succeeds, it does NOT certify
Theorem 1.1, because `Theorem1_1_Goal` has no proof. It establishes only
that **the included theorem declarations** are accepted by Lean.

There are no imports from the third-party Lean proof repository, no
project-specific `axiom`, and no `sorry` or `admit` in Lean source.
The `Lemma33Reviewed.lean` code adapts a published Apache-2.0 source and
is **attributed**. It should not be called independently authored.

## Reproducibility and limitations

The container producing this ZIP has neither `lean` nor `lake`, and internet
DNS resolution failed, so **no kernel-build PASS claim** is made here.
See `KERNEL_BUILD_STATUS.md` and the GitHub Actions workflow to obtain
an actual kernel check on your machine / GitHub.

To see a nonzero proof-completeness gate run:

```bash
python3 tools/certify_complete.py
```

That gate intentionally **fails**, because the main theorem is not yet proved.
