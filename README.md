# OpenAI #086 — independent Lean 4 proof development

**Status as of 2026-11-19: INCOMPLETE, and not kernel-verified in the authoring runtime.**

This project studies the user's 93-page PDF, *An L³ Bound for the Trilinear Hilbert Transform* (5 October 2026), using the original minus-shift operator with slopes `1,2,3`. Its complete theorem is encoded in `OpenAI086/PaperStatement.lean` as `Theorem1_1_Goal : Prop`, **without a proof term**.

No `TrilinearHT` dependency, external proof bridge, or copied Rademacher–Menshov Lean implementation is bundled in this independent edition. The older adapted `Lemma33Reviewed.lean` and the dependent `full-theorem/` package have intentionally been excluded. The repository depends on ordinary Mathlib.

## Exact scope

The paper contains **59 individually numbered results** (45 lemmas, 9 propositions, 3 theorems, 1 corollary, 1 definition). `verification/PAPER_RESULTS_INDEX.md` and `.json` provide a page-resolved register of every named result. A status of PARTIAL means that *some particular implication, simplified model, or intermediate lemma* has source code. **Zero of the 59 full paper results is certified by this repository at present.**

### Independent Lean components added in this edition

| Module | Paper relation | Precise coverage |
|---|---|---|
| `ArbitraryDepthTelescoping.lean` | Lemma 3.3 | Exact ordered telescoping with an arbitrary number of noncommuting layers; no logarithmic estimate |
| `OrderedProductTelescoping.lean` | Lemma 3.3 | Explicit three- and four-layer ordered identities |
| `FiniteStoppingSets.lean` | Lemma 2.4 | Four-family finite-set union cardinality bound; not the measure-theoretic stopping construction |
| `FiniteMarginalCancellation.lean` | Lemma 2.4 | Discrete finite-difference endpoint cancellation; not the smooth Gevrey kernel |
| `PathLabelEnergy.lean` | Lemma 3.4 | Exact finite path-label energy bound `D³`; not the cell-dependent compression theorem |
| `QuadraticChartsElementary.lean` | Lemma 4.2 | Quadratic translations, affine rescaling, products for the `d=0` chart |
| `EntryRankSummation.lean` | Lemma 8.5 | Harmonic rank-summation step assuming per-rank incidence bounds; not the full nested-set lemma |

This is a substantive extension of the previously provided algebraic, combinatorial and finite projection components. It does NOT establish the paper's central analytic estimates in Sections 2–10.

## Dependencies and exact target

- `lean-toolchain` pins the intended Lean version.
- `lakefile.toml` pins a Mathlib commit.
- `OpenAI086.lean` imports all independently authored modules.
- `OpenAI086Whole.lean` imports that entrypoint and prints selected axiom dependencies.
- `OpenAI086/PaperStatement.lean` defines the principal-value truncation and unproved `Theorem1_1_Goal`.

The root library deliberately has **no** `MainProof.lean`. To close the theorem, it must be added with a proof of the exact local target, rather than importing the published result from the external project. The paper's full bounded extension to `L³` also requires an explicit formalization beyond the present Schwartz proposition.

## Run on Ubuntu/WSL

Install Git, elan/Lean, and Python with NumPy and SymPy. An initial internet connection is required to obtain the pinned Lean and Mathlib versions.

```bash
python3 -m pip install sympy numpy
lake exe cache get
bash verify_all.sh
```

`verify_all.sh` runs import checks, source placeholder safety, the 59-item gap report, symbolic/numerical sanity checks, then `lake build OpenAI086Whole` and a direct Lean entrypoint check. The numerical tests are **not** proofs. A successful build checks only existing **intermediate** theorem declarations.

The strict certification command is intentionally separate:

```bash
bash verify_paper_complete.sh
```

It **must fail** until independent kernel-checked proofs of all required obligations and the exact main theorem have been supplied. See `tools/certify_complete.py` and `tools/paper_obligation_report.py --require-complete`.

## Verification and limitations

A successful source audit is not a Lean elaboration, and a Lean elaboration of a `def ... : Prop` is not a proof. No `sorry`, `admit`, `axiom`, `opaque`, `constant`, `unsafe`, or `native_decide` is permitted in authored Lean source; `tools/lean_source_safety.py` checks for such keywords after stripping comments and strings.

This authoring runtime did not have `lean` or `lake` and could not download them. Compilation and theorem axiom reports therefore remain unverified. GitHub Actions `.github/workflows/lean-proof-audit.yml` runs the build when uploaded to GitHub.

See `PROOF_STATUS.md`, `PROOF_DEPENDENCIES.md`, `verification/PAPER_RESULTS_INDEX.md`, and `PROVENANCE.md` for audit details.

## Continued independent work: 2026-11-19, Sections 8--9

Five new Lean modules have been added and imported into the entrypoint:

- `OpenAI086/ComponentIntersections.lean`: actual finite-set inclusion/exclusion, strict majority intersection, and the quantitative `> |F|/10` overlap under the exact 1.1 / 1.1² size conditions in the proof of Lemma 8.10.
- `OpenAI086/EntryRankConcrete.lean`: derives the harmonic entry-rank bound from incidence counts and denominator monotonicity; the ranking construction for an arbitrary chain of finite sets is still open.
- `OpenAI086/SparsePairBudget.lean`: global `sum_s N_s ≤ L*M²` pair-incidence count and restriction to retained scales (the first counting step in Lemma 9.1).
- `OpenAI086/SparseBlockAccounting.lean`: conditional numerical count of greedy scale blocks. Construction of the blocks and their mass bounds remains open.
- `OpenAI086/ColoredPathUniqueness.lean`: distinct proper-edge-colored four-step paths from a fixed start have distinct ordered color sequences, allowing repeated vertices.

`tools/test_continuation_finite.py` checks exhaustive small finite sets, exact rational rank/graph budgets and four-edge path uniqueness. Neither these tests nor the static audit substitute for `lake build`.

**Still open:** kernel compilation; Lemma 3.3 logarithmic inequality, Lemma 3.4 full projection compression, the quantitative analytic estimates of Sections 4--9, the complete counting lemma's power saving, Proposition 2.3, Theorem 2.2 and Theorem 1.1. This repository does NOT yet formalize the full paper.
