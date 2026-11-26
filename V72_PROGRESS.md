# V72 — Paper-side event energy and local-form integration

Source-only continuation of V71. The two new modules contain 25 theorem candidates and 9 new definitions (see source map). The Lean compiler and numerical verification suites were not run, at the user's request. Prior Lean sources, original paper, and pinned reference archive are preserved. These are adaptations of the attributed Apache-2.0 reference proof, not an independent Mathlib-only proof.

## Section 8, Lemma 8.7 / Proposition 8.9

`PaperEventEnergy.lean` transfers the geometric separation and projection arguments to `paperSideEvents` (the actual paper-specific predicate from V71). It constructs finite event families, gives their membership and sum decomposition, proves pairwise disjointness and height-zero nonadjacency for different components on the same pre-cell, and proves the individual projection/subtotal leakage estimate. It adapts longest-chain level partition and Bessel rows; the scheduled group theorem uses `paper_chain_length_valid` rather than the old ratio-based chain theorem. The new chain bound is the exact floor of `2*(v57FloorLog M + 40*dmax*harmonic M)/delta`, with the factor of six from three block classes and the two-fold row bound. It proves block subtotal almost-orthogonality and the group side energy estimate with the row output and error sums on the right. This still requires composing the rows with the actual global lift and bounding the full paper-side numerical errors, and is not the final global Proposition 8.9.

## Sections 8–9, exact local form decomposition and role masks

`PaperLocalForms.lean` partitions the actual minimal PRE components using `paperCoreComps = allComps \\ paperSideEvents`; proves the frozen-evaluation/core/side identities at the block level; defines the paper-good component predicate and bounds bad heights using V70. The paper-specific core on a cell is the actual sum of its retained pre-cell components. The side term is adjusted by the old-core minus new-core difference; `paper_block_balance` and `paperSideAt_basic` identify it with the actual rolling coarse-output difference plus the new side block subtotal. The physical output splits exactly into the new core, side and unchanged error. The actual `fp.Λc I` expands over all core/side/error patterns and each pattern admits the first-success HasSum on actual component subtotals. Noncore slots use a dummy good entry. This supplies the local-form mask identity, not the subsequent estimates after Fourier expansion or fixed offsets.

## Still open

- Sections 2–3: exact local kernel, outer reduction, compression and corrected-height correspondence.
- Section 4: exact LSS inverse theorem and pooled Fourier tails.
- Sections 5–6: delayed fits, adaptive schedules, original graph/masks/helper filters.
- Section 7: weighted maximal theorem and actual stack budgets.
- Section 8: composed global lift rows for the new event family, negligible errors and global side energy; first tops with original type classes.
- Section 9: apply role masks to progression torus reductions, side-offset Fourier expansions, sparse counts and error budgets.
- Section 10: establish actual analytic reserves and integrate final parameter choice.

The printed false Lemma 3.5(2) remains corrected, and the main theorem remains the existing reference-backed candidate. No claim of elaboration, kernel acceptance, or full-paper completion is made.
