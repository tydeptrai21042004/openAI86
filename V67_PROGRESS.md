# V67 — Section 7 and Section 10 source candidates

This is a continuation of V66, not a completed formalization. No Lean compilation or numerical regression tests were performed, as requested.

## Added mathematical source

- `side_size_of_path` derives the normalized individual side bound directly from the path-square cap, using the left endpoint of the actual dyadic cell and nonnegative nested sums.
- `three_side_power` establishes an **unclipped** length-weighted p-power bound on the reference's actual pattern expansion for p > 2/3. This strengthens the clipped formulation for purposes of the paper's Proposition 7.5. The core bound and path-square cap remain hypotheses.
- `variation_colored` establishes the factor m for a supplied m-color decomposition of certified depth intervals, by applying the existing VarCap to each color. An interval coloring construction for arbitrary bounded-overlap families is not included.
- `near_gain`, `depth_power_reserve`, and `absolute_near_gain` give the arithmetic in Section 10.3 for the paper's exponent C19(q-2), retaining the absolute near-band cost and the finite-depth constant. The required analytic overhead and polynomial block-depth bounds remain hypotheses; these are not a proof of all original parameter choices.

## Open obligations

- Section 2: exact local admissible kernels and outer reduction correspondence.
- Section 3: remaining compression correspondence; corrected Lemma 3.5 must be used downstream.
- Section 4: exact LSS Theorem 4.7, pooled Fourier tails, original chart data.
- Section 5: delayed projections, adaptive schedule and restart data.
- Section 6: original graph, mask, and helper-filter correspondence.
- Section 7: exact general weighted mixed-norm maximal theorem (Lemma 7.1), interval coloring for arbitrary bounded overlap, stack and near-band correspondence, establishment of actual path-square cap.
- Section 8: original graph energy and all geometric hypotheses.
- Section 9: progression parameter and numerical error correspondence.
- Section 10: establishment of the overhead reserves and complete original parameter integration.

All new declarations are uncompiled candidates. The original PDF, pinned reference archive, locked main theorem and independent proof registry are unchanged. The reference-backed main theorem is still separate from the independent and exact-paper proof goals.
