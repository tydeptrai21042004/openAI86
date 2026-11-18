> **Whole-project packaging update:** The new `OpenAI086Whole.lean` entrypoint imports the Lemma 3.3 candidate and core together. Theorem 1.1 remains unproved, and kernel compilation has not been confirmed in this environment.

# Exact proof status for OpenAI #086 (5 October 2026 PDF)

This is a **research artifact, not a complete independent formalization**.

| PDF | Key target | Independent Lean status |
|---|---|---|
| Introduction | quadratically resonant four-term phases | Source proof (algebra) |
| 2.1 | local absolute-form estimate using two-coordinate Jacobian and interpolation | Geometry only; analytic estimate MISSING |
| 2.2 | uniform local estimate independent of number of depths | MISSING |
| 2.3 | normalized absorption estimate for the full local forms | MISSING; scalar absorption only |
| 2.4 | reconstruct singular kernel from local estimates | MISSING; pointwise sign reversal only |
| 3.1 | packing of attempts | Scalar generation inequality only |
| 3.2 | coefficient uniqueness and projection bounds | Private-coordinate finite model only |
| 3.3 | products of nested Hilbert-space projections | NEW: coordinate-mask special case; noncommuting product MISSING |
| 3.4 | quantitative projection compression, depth-independent | MISSING |
| 4 | quantitative Weyl alternative, quadratic charts and detection | Phase algebra only; quantitative inverse theory MISSING |
| 5 | two-accuracy predictor and delayed projections | Scalar predictor correction only |
| 6 | localization by quadratic curvature | MISSING |
| 7 | short depth blocks and side terms | MISSING |
| 8 | coherent modes, energy, projection rows | Last-endpoint set inclusion correction only |
| 9 | sparse count and successful-height lemma | First-failing-role logic only |
| 10 | choose parameters, sum scales, pass to principal value | MISSING |
| Theorem 1.1 | L³ × L³ × L³ to L¹ bound of trilinear Hilbert transform | PROPOSITION DECLARED; **NO LEAN PROOF** |

**Note:** The underlying paper states the main theorem for Schwartz inputs and deduces a unique bounded extension. The present definition `Theorem1_1_Goal` requires pointwise principal-value convergence and an L¹ estimate. It is **not** a theorem proved by this project. In particular, a successful `lake build` would NOT establish it.

The entire repo consists of newly written toy/sublemma formalizations. It does not import or embed a previously published Lean formalization of the trilinear Hilbert transform. It does import ordinary Mathlib.

## Additional reviewed independent modules (this revision)

- `NoncommutingProducts.lean`: Exact ordered-product telescoping for arbitrary
  noncommutative rings and a coarse norm bound for normed rings. These are
  useful building blocks for the telescoping in Lemma 3.3, **not** Lemma 3.3.
- `NoncommutingProjectionExample.lean`: Two genuine, noncommuting orthogonal
  projections on `ℝ²` with squared-norm contractions.
- `PrefixCombinatorics.lean`: Exact splitting of consecutive finite prefixes,
  which precedes dyadic block decompositions.
- `PRE_MERGE_REVIEW.md`: Before-integration assessment of the reference Lean
  sources and explicit accept/reject decisions for each remaining claim.


### Lemma 3.3 logarithmic candidate, reviewed integration

`OpenAI086.Lemma33.nestedProjectionProduct_prefix_rows_sq` and
`OpenAI086.Lemma33.nestedProjectionProduct_successive_jumps` provide
actual Lean proof scripts for the main bounds in a common-codomain
setting. The module is an adapted, credited code proof, not an independently
developed proof; kernel compilation pending. Varying row codomains
and exact final PDF-level generality remain unproved in this project.

The candidate is not imported by the normal aggregate target pending
`lake env lean OpenAI086/Lemma33Check.lean` success.
