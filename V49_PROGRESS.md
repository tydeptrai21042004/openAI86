# V49 — Active-anchor history coherence and row-error assembly

Source basis: October 5, 2026 manuscript, Lemma 3.4, pp. 11–13.

## New independent Lean modules

- `OpenAI086/PaperV49AnchorCoherence.lean`
  - Proves that if two terminal cells have the same spatial ancestor at a current anchor depth, then their coefficient paths agree at all earlier depths.
  - Uses the actual first-match recurrence `v47AnchorDepth` / `v47AnchorList` to show their selected-anchor depth histories through that depth agree.
  - Strengthens this to equality of the complete earlier `(depth, spatial-cell)` anchor history.
  - Proves the immediately preceding anchor label is determined by the current active-anchor cell. This is the key coherence fact needed to collapse V48's history-labelled refinement to the paper's active-anchor atoms.

- `OpenAI086/PaperV49ErrorRows.lean`
  - Formalizes the exact finite Hilbert-space row-error estimate from p.12: rowwise coefficient error `sum_v ||e_{r,v}||² <= (tau*a)²`, Bessel row contraction, and integrated column-energy bound `sum_v ||Phi_v||² <= D³ |R|` imply total squared error at most `tau²*a²*D³*|R|`.
  - Reuses the already proved finite complex Cauchy–Schwarz/Bessel double-sum theorem rather than assuming the desired error conclusion.
  - Exposes the two-budget attempt/row assembly as a paper-named theorem.

## Exact scope

The new history theorem addresses the V48 over-refinement issue at the level of active-anchor cells: equality of the current anchor cell forces equality of all earlier coefficient decisions and earlier anchor cells. The stage-partition quotient and its measurable partition/projection realization are still separate obligations.

The row-error theorem proves the algebraic double-sum estimate under the explicit pathwise integrated column-energy premise. It does not construct the actual local operators `B_nu`, nor derive their Bessel contraction or the `D^3` column budget from the paper's spatial tree. Those remain upstream hypotheses to be discharged by the concrete construction.

## Validation performed

- Static import and reachability audit.
- Registry consistency audit.
- Source safety scan; no new `sorry`, `admit`, or custom mathematical axioms.
- Deterministic exact-model tests for anchor-history coherence and the row-error inequality.
- ZIP integrity check.

These are not Lean kernel certificates.

## Kernel disposition

Lean, Lake, and elan are absent in this environment; the pinned Lean toolchain cannot be installed because DNS/network retrieval is unavailable. All V49 targets remain `BLOCKED`, and no manuscript result is promoted to kernel-certified.

## Remaining Lemma 3.4 work

1. Build the exact stage partitions from active anchor cells plus terminal cuts and prove the partition quotient is measurable.
2. Construct the local direct-sum projection families on these exact atoms and prove their nesting.
3. Identify each concrete `(Z_n - Z_{n-1})(1_R g_K)` with the actual augmented-column coefficient increment almost everywhere.
4. Discharge the Lemma 3.3 variation hypothesis for those concrete products.
5. Derive both `D^5` representative-energy caps from the actual scalar moment identity and cut-cell construction.
6. Integrate the pathwise column-energy budget and Bessel row contraction for the actual row operators.
7. Assemble size segments, attempts, anchor terms, error terms, complements, and finite-measure averages to obtain the complete Lemma 3.4 statement.

After Lemma 3.4, continue the corrected vector/supremum conclusions of Lemma 3.5, Lemma 4.3, Theorem 4.7, Sections 5–6, Section 7, Proposition 8.9, Lemma 9.1, Proposition 2.3, and Theorem 1.1.

No paper result counts change: 0/58 numbered mathematical results are kernel-certified; Theorem 1.1 remains unproved.
