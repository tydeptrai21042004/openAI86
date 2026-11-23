# Independent Lean continuation V10 — 2026-11-22

Source: `paper(4).pdf`, *An L³ Bound for the Trilinear Hilbert Transform* (93 pages).
Based on the complete `openAI86_V9_Independent_Continuation_FULL.zip` repository.

## Added mathematical components (5 modules)

| New source | Mathematical result | Still missing |
|---|---|---|
| `OpenAI086/BadDensityThreshold.lean` | Proof candidate: a positive **integer** gap or an exceptional-density threshold gives a pointwise bad-height indicator bounded by the two gaps plus `fraction/β` | Actual floor-log and label hypotheses |
| `OpenAI086/FiniteBadHeightSet.lean` | Proof candidates: monotone cardinal rank under `Finset` inclusion; direct pointwise bad-height indicator bound from `Pold ⊆ Pnew ⊆ C` | Global rank enumeration and density count in original paper |
| `OpenAI086/HeightPositionChainBridge.lean` | Proof candidates: REAL interleaved position-gap telescope; both position and height telescopes combined in the finite chain count | Exception incidence derivation |
| `OpenAI086/RankedTwoAxisChain.lean` | Proof candidate: exception incidence budgets derived from concrete per-rank occurrence and rank-size assumptions on **both axes**, using V9 height-lag theorem | Derive and synchronize those ranks from the manuscript's actual changing finite sets |
| `OpenAI086/FiniteSparseChoiceRows.lean` | Proof candidate: row-dependent ordered noncommuting projection products, when rows choose from K predetermined depths, obey `sum |Bᵣ Z_{depthᵣ}x|² ≤ K ‖x‖²` | Logarithmic bound with *every* depth permitted, as in full Lemma 3.3 |

### Exact target/assumption improvements

1. Unlike V9, the **per-height interleaved log-gap budget** in the chain proof is now derived, not assumed. This depends on explicit `P_i ⊆ C_i ⊆ P_(i+1)`, including the last endpoint `P_N ⊆ C_N` omitted from the original displayed hypotheses.
2. Both exception totals are controlled by individual-label occurrence counts and entry ranks, via `ranked_exceptional_density_le`. The remaining pointwise predicate is also derived independently from actual nested `Finset` labels (`finite_bad_height_from_nested_sets`). The missing formal link is an explicit enumeration of labels/ranks from changing `P_{i,h}` / `C_{i,h}`, plus their physical exceptional-count hypotheses.
3. `finite_sparse_choice_noncommuting_row_bound` has no loss in the *maximum numerical depth*. When the set of candidate depths contains K indices, it costs K in squared energy. This does **not** replace Lemma 3.3's `log₂(T+1)^{2m}` loss in a dense set of choices.

### Verification

`tools/test_v10_two_axis.py`: **11,976 checks pass** (10,476 finite exact integer/rational cases plus 1,500 floating-point noncommuting-projection checks). Static reachability and source-safety checks pass. The theorem inventory still has **59 paper results, 21 with partial components, 38 with proxy goals, and 0 fully independently kernel-verified**.

**No installed `lean`, `lake` or `elan` and no outbound network:** the new Lean source is NOT compiled or kernel-verified in this environment. It may have typechecking/tactic errors. Do not cite the V10 source as a completed formal proof until `lake build OpenAI086Whole` actually succeeds and the `#print axioms` audit is inspected on Ubuntu or CI.

### Run

```bash
cd openAI86-main
./verify_smoke_v10.sh
```

If Lean/Lake is not installed, the script runs source and finite tests then exits with **code 2** (explicitly unverified). After installing the pinned toolchain, it also compiles the project. The GitHub Actions workflow includes V10 tests.

### Remaining priority

1. Make the 5 new modules **compile** in pinned Lean 4/mathlib; fix failures without weakening statements.
2. Finish actual variable-prefix/logarithmic estimate in Lemma 3.3 (requires aligned dyadic block orthogonality for multiple noncommuting layers).
3. Formalize Lemma 8.6 as one theorem quantified over the paper's actual `P`, `C`, `X`, `Y` finite label sets and floor-log ranks; eliminate the rank-incidence and predicate interfaces by proving them from its stated hypotheses.
4. Lemmas 3.4, 5.3, 9.1, Proposition 2.3, Theorem 2.2 and Theorem 1.1 remain unproved in this independent repository.

None of the modified files imports the published Roos formalization. Reference-only modules stay quarantined under `verification/reference_only/`.
