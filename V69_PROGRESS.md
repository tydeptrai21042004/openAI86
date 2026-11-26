# V69 — Normalized component sizes and first-top budgets

Source-only continuation of V68. Five new theorem proof candidates; no Lean compilation or numerical regression tests have been performed. The reference and original paper are unchanged.

## Section 8

- `normalized_component_comparison`: combines the two actual reference component inequalities of Lemma 8.11 on the same actual cell and with the same frozen coefficients. Divides the side estimate by the cell length. Converts the reference error `3 Bc / Dstar^59` to `Dstar^-50` under the explicit reserve `3 Bc <= Dstar^9`.
- `coefficient_reserve`: derives this reserve from the reference frozen coefficient bound `Bc <= 4 Dstar^2 CF` and the stronger normalization inequality `12 CF <= Dstar^7`. The latter is not proved for the actual global parameter choice here.
- `actual_bin_bound`: counts distinct representative labels in a dyadic amplitude bin on actual retained reference uses. The global label bound comes from `usedReps_le_Dstar`, the middle range from the tested dyadic thresholds `dyThr_spec`, the low range from `Dstar <= M/sigma^2`, and the high range from the supplied amplitude cap. The tested count estimate, path bound, amplitude cap and representative instance property must be supplied. This is a reference-class result, not a correspondence proof for the printed base-1.1 types.

## Sections 8.10 and 10.3

- `top_test_card`: bounds the product of heights, two dyadic type ranges and actual dyadic threshold set by H^4 using the reference threshold cardinality theorem.
- `first_top_polynomial`: collects the actual reference top-count prefactor into `96 H^7` provided the energy bounds, number of blocks/depths, number of tests and inverse cut fraction satisfy the displayed common reserves. This does not prove those analytic hypotheses.

## Remaining source work

- Section 2: original local-kernel and outer-reduction correspondence.
- Section 3: compression and corrected-height downstream correspondence.
- Section 4: exact LSS inverse theorem and pooled Fourier tails.
- Section 5: delayed projections and adaptive schedules.
- Section 6: original graph, masks and helper filters.
- Section 7: exact weighted maximal theorem and actual stack-energy hypotheses.
- Section 8: original base-1.1 type classes, geometric event density, actual energy hypotheses, original first-top normalization reserves and amplitude cap.
- Section 9: exact original progression parameters and error budgets.
- Section 10: establish analytic overhead bounds and integrate the parameter choices.

No claim of whole-paper completion. The printed Lemma 3.5(2) still requires its dimension-dependent correction. The reference-backed main theorem candidate is unchanged.
