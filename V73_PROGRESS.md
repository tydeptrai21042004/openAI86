# V73 — Paper-specific global lift and rolling side energy

Source-only continuation of V72; seven theorem candidates and one new definition. No Lean elaboration, kernel replay or numerical testing has been performed. All prior Lean modules, the original PDF, and the pinned reference archive are preserved. The two new modules are attributed adaptations of the Apache-2.0 reference proof, not independent Mathlib-only proofs.

## Sections 8.7–8.9: global lift and event leakage

`PaperGlobalEnergy.lean` adapts the complete class count, group count, global error summation and linear-energy proof bodies of reference Sec13_3 to the exact `paperSideEvents`, `paperEvents`, and `paperBlockSide` from V71–V72. The same chain-length floor is used throughout:

`L = floor(2 * (v57FloorLog M + (4*dmax)*harmonic M/(1/10)) / delta_s)`.

- At any point y in a group, the count of events is at most `3*(L+1)*|ptSet y|`. Across groups, the original path budget bounds the total event count by `3*(L+1)*floor(Dstar)`.
- The single event leakage satisfies `err^2*Dstar^397 <= Bc*|J|`, using actual frozen coefficients and the reference's pair-constant estimate. Summation on the root gives `sum err^2 * Dstar^396 <= 3*(L+1)*Bc*|R|`.
- `paper_linear_energy` chooses frozen coefficients from `frozen_coeffs`, applies the V72 scheduled paper Bessel-row theorem to the global lifts using `lift_composition_dep`, and sums the above leakage errors. The conclusion is `sum ||paperBlockSide||^2 <= 24*(L+1)*(G0+2*CF/Dstar^394)*|R|`, with the same explicit `G0` as in the reference. This addresses the global linear-side energy at the reference schedule, conditional on all the explicit geometric, lift, path, gauge, normalization and history assumptions of that theorem. It does not yet construct these data for every original manuscript attempt.

## Sections 7–9: actual rolling side states

`PaperRollingEnergy.lean` defines `paperSideState` as physical coarse output minus physical frozen output plus the new paper block subtotal. It adapts the two existing rolling budget arguments using the same `rolling_budget` and `rolling_budget_blocks` proofs. On arbitrary certified depths, the side subtotal is charged at most K times; on block starts, it is charged once. `paperSideAt_eq_restrict_state` identifies the restriction of this exact state with the side input of the V72 local-form expansion for a basic (non-U) slot. The bounds still require supplying actual frozen coefficients, matching schedule choices, and all rolling/lift hypotheses consistently in a final attempt construction. They do not establish the exact weighted maximal theorem or all stack hypotheses.

## Remaining obligations

- Sections 2–3: exact local kernel, outer reduction, compression and corrected-height correspondence.
- Section 4: exact LSS inverse theorem and pooled Fourier tails.
- Sections 5–6: delayed fits, adaptive schedules, original graph/masks/helper filters.
- Section 7: exact weighted maximal theorem and use the new side budgets in both fixed stacks and near-band estimates.
- Section 8: instantiate the new global energy theorem on actual attempt data, exact first tops and remaining original analytic budgets.
- Section 9: torus progression normalization, side-offset Fourier expansion and sparse counts for the paper-specific masks.
- Section 10: establish actual reserves and integrate final parameter choices.

Lemma 3.5(2) remains corrected. The original main theorem entry point is unchanged. Full-paper source completion is not claimed.
