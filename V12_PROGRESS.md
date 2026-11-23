# V12 — Exact cardinality logarithm and a concrete two-axis chain bridge

**Source:** `paper(4).pdf`, *An L³ Bound for the Trilinear Hilbert Transform* (5 October 2026), especially Lemma 8.5 (PDF p. 69) and Lemma 8.6 (PDF p. 70).

The V11 repository remains the sole code base for these independent changes. No proof is imported from the public external Lean formalization.

## Changes

| New Lean source | Mathematical work | What is still required |
| --- | --- | --- |
| `IntegerLogExact.lean` | Proves `(k+10)10^k ≤ 10·11^k`; every qualifying threshold `11^(k+1) ≤ n·10^(k+1)` occurs at `k < 10(n+1)`; proves window invariance, downward closure of thresholds, and a finite bound on the integer rank. | A full arbitrary-set end-to-end proof still needs the label-ordering step. |
| `ConcreteIntegerLogBadDensity.lean` | Instantiates the V11 concrete bad-height chain with `integerLogBin11_10` and derives rank caps from actual set cardinalities. | It retains aggregate exceptional-fraction hypotheses, which are eliminated only in the next specialized bridge. |
| `ConcreteRankedIncidences.lean` | Converts actual normalized `|(E∩S)|/|S|` into finite indicator sums and derives a harmonic bound from per-label multiplicities and first-entry rank-size assumptions. | It takes rank-size assumptions as explicit conditions; it does not construct first-entry permutations for arbitrary label sets. |
| `ConcreteRankedLogChain.lean` | Combines both axes, the actual UNION bad-height indicator, concrete base-1.1 bins and per-label incidence bounds in a single statement. | It uses one fixed `Fin M` rank order; the paper's two axes may require separate enumerations. Also assumes positive bad-height density and absorption. |

The new chain theorem does **not** postulate an abstract pointwise bad-height inequality, unspecified monotone rank, or global exceptional-density budgets. Its remaining first-entry rank hypotheses are displayed in the theorem signature. It does **not** prove the full Lemma 8.6 under the PDF's original hypotheses, notably the missing terminal inclusion or the initial `h < Δ` counting regime. The PDF's omitted `P_N ⊆ C_N` condition remains explicitly repaired in the finite-set formulation.

## Tests

- **57,490 V12 exact checks passed.** `tools/test_v12_exact_log_chain.py` checks Bernoulli bounds, completeness and window invariance of the rank, downward closure, normalized exceptional-count bounds, the real union predicate, pointwise inequalities and a non-vacuous chained instance, entirely with exact integer/rational arithmetic.
- `verify_smoke_v12.sh` runs the independent source audits and focused legacy regressions, then attempts `lake build OpenAI086Whole` if Lake is available.
- On the current environment the smoke script returned **2** after all source and finite-regression checks passed: Lean/Lake are absent. Exit code **2** after passing the source/numeric stage means the Lean kernel was **not** run. Only a successful kernel build can certify any Lean theorem.

## Open mathematical goals

1. **Lean kernel:** install pinned Lean and Mathlib, compile all V9–V12 modules and fix elaboration/tactic errors as necessary.
2. **Lemma 8.5:** construct the first-entry enumeration for arbitrary nested `Finset` families; do this separately in the height and position directions, and remove the fixed-order rank hypotheses of V12.
3. **Lemma 8.6:** formalize the PDF's initial bad-height (`h < Δ`) count and strict density/absorption bookkeeping, then prove the lemma with its appropriately corrected last-position inclusion.
4. **Lemma 3.3:** full logarithmic row-dependent noncommuting prefix bound is still open, as is Lemma 3.4 compression.
5. **Theorem 1.1:** no complete independent proof has been produced or kernel-certified here (0/59 manuscript results completed).

## Ubuntu / WSL

```bash
unzip openAI86_V12_Independent_Continuation_FULL.zip
cd openAI86-main
./verify_smoke_v12.sh
```
