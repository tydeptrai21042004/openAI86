# V65 — quadratic chart and detection continuation

Seven new reference-backed source declarations in three Lean files. The original paper, independent library, and pinned reference archive are unchanged. No Lean compilation or regression tests run; proof candidates may require elaboration repairs.

- Definition 4.1 / Lemma 4.2: `affine_conjugate_product` combines two independent affine pullbacks, conjugation, and the block product. Bound `chartTranslationBudget H ^ 6` is independent of all real affine parameters. `linear_chart` explicitly realizes an arbitrary real linear phase as a bounded dimension-zero chart.
- Lemma 4.4: `restore_chart_phase` turns a phase-removed HasSum into the original phased series. The reference `splitFourierExpansion` supplies fixed-splitting tails; the pooled-envelope statement and a full original splitting-data bridge remain open.
- Lemma 4.5: `progression_all_dimensions` pads both input charts with a unit atom and applies `progressionSeparation`. This removes the positive dimension restrictions, retains coefficient mass, tail, complexity, and cardinality bounds, at the cost of padding dimensions and using `max H W₀ ^ 6`. The wrapper does not retain the explicit time-chart parameter identities (they hold for padded reference data and need a separate projection back to the paper's data). The fixed Gevrey order may increase. The reference's quantitative bound is retained, not silently identified with the paper's budget.
- Lemma 4.6: `separated_kernel_atoms` turns both separated characters into bounded charts of dimension zero and complexity exp(2), with exactly the reference's finite cardinality, coefficient mass and uniform error estimate. The separate bilinear norm estimate is `Auto.separated_form_le`, and the effective quadratic/frequency statement is `Auto.separatedPhase`; these are not yet bundled with the original slot factors and support data.
- Lemma 4.9: `continuous_inverse_bilinear` conjugates the bounded chart returned by `Auto.continuous_inverse`, with no cost in complexity, to obtain a bilinear moment in the paper convention. Uses the reference's alternative discrete inverse machinery; this does not reproduce Theorem 4.7.
- Lemma 4.12: `detection_bilinear` gives the same bilinear conversion for the actual local form and arbitrary distinct slots, retaining the quantitative budget and absolute exponent independent of q.

## Source navigation (existing reference proofs, not new declarations)

| Paper result | Reference declaration | Remaining correspondence |
|---|---|---|
| 4.1 | `Auto.QuadraticChartData`, `Auto.QuadraticChartComplexity` | Compare Gevrey coordinate words to multi-indices; original complexity convention |
| 4.2 | `Auto.quadraticChart_affine_closure`, `Auto.productQuadraticChart_complexity` | General multivariable closure |
| 4.3 | `Auto.weylSplitting` (V59 adapter) | Original chart and kernel correspondence |
| 4.4 | `Auto.splitFourierExpansion` | Pooled envelope across rational choices |
| 4.5 | `Auto.progressionSeparation` | Padded curvature parameter correspondence |
| 4.6 | `Auto.separated_form_le`, `Auto.separatedPhase`, `Auto.separatedKernelApprox` | Joint original slot factors and parameter identities |
| 4.7 | No exact LSS proof supplied | Full external nilmanifold theorem |
| 4.8 | `Auto.cubeAverage_three_le_L2`, `Auto.intervalL2GowersSeminorm_toLp` | Exact cube normalization and continuity bridge |
| 4.9 | `Auto.continuous_inverse` | Original chart convention, alternate proof |
| 4.10 | `Auto.continuous_decomposition` | AE equality on normalized interval vs original functions |
| 4.11 | `Auto.vonNeumann_local_L2`, `Auto.vonNeumann_local_L1` | Original interval norms and kernel data |
| 4.12 | `Auto.detectResidual` | Original kernel data |

`verify_v65.sh` includes the new declarations for later replay by the user. The older audit files are historical and unchanged. Whole-paper source remains incomplete, in particular exact 4.7, the pooled tails of 4.4, and Sections 5–10 correspondence.
