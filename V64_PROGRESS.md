# V64 — source-level continuation

V64 preserves V63 and adds seven uncompiled theorem candidates in three files. No new kernel verification, regression tests or certification were attempted, per the user's request. The full paper remains incomplete.

## Lemma 3.4, averaging clause
`external_main_theorem/v64/CompressionAverage.lean`: weighted Bochner averaging in the dependent finite Hilbert direct sum, followed by application to the actual ordered projection/complement product via V59. The bound is the existing uniform compression constant times the L1 norm of the common complex weight. This covers finite positive measure and signed/complex densities relative to a positive measure, assuming the weighted row vector is Bochner integrable and the row codomains complete. It does not claim to construct measurable families of masks or establish integrability for every possible parameterization. The original normalized analytic data correspondence of V59 is still required.

## Lemma 3.5 and Lemma 8.2
`source_fidelity/v64/PaperExceptional.lean`: defines the printed exceptional radius predicate, derives the log-window inequalities, then applies the existing packet cover to the actual filtered block schedule. The resulting count is 5d, the constant in the printed proof. This is the first clause of Lemma 8.2 for a primary with an arbitrary real frequency vector and natural height bound.

`external_main_theorem/v64/HeightCorrespondence.lean`: bridges the unreduced rational representation of the manuscript's height values to the reference's reduced rational heights. Proves the equality of the two exceptional predicates at integral height H; applies the reference tiny-span theorem on nonexceptional paper blocks. The explicit numerical separation inequality required by the reference Cramer estimate remains a hypothesis. This is not yet a proof of the original schedule's entire parameter selection.

## Downstream audit of Lemma 3.5
The direct later citation is in Section 8.3 (packet width) and Lemma 8.2 (at most dmax packets). These use part (1), not the false dimension-free annular bound in part (2). The new count does not invoke that false statement. This direct-citation audit is not an exhaustive proof of every implicit use of scale bounds in the manuscript.

## Remaining work
- Theorem 4.7 exact LSS theorem: still open.
- Sections 4–6: chart calculus, quantitative detection, exact adaptive construction, localization correspondence.
- Lemma 3.4: original analytic data correspondence and arbitrary parameterized integrability, as appropriate.
- Lemma 8.2: exact schedule parameter inequality and primary correspondence beyond the rational predicate.
- Sections 7–10 and outer reduction: original geometry, energy budgets, exact parameter selection and final integration.
- Lemma 3.5(2) must be corrected, not proved as printed.

V64 is a source package only. A candidate can contain Lean elaboration errors. `verify_v64.sh` is provided for later user replay; preparation/build were not run in this revision. No previous verified status is upgraded.
