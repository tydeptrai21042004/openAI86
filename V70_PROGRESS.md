# V70 — Manuscript base-1.1 components and common heights

Source-only continuation of V69. The three new Lean modules are uncompiled proof candidates. No Lean compilation or numerical regression suite was run. Prior Lean sources, paper and pinned reference are unchanged.

## Actual printed predicate and Lemma 8.4

`PaperGood` uses equality of the floor of the base-11/10 logarithm of PRE and CURRENT primary counts, plus the nine-tenths primary-good test. `PaperCore` uses the full-range bad-height count of that exact predicate. These are separate from the weaker ratio-based reference predicates. `floorlog_ratio` proves equal types imply `10*b < 11*a` for positive `a`; hence `PaperGood` implies reference `Good`, but the reverse is not used.

`paper_good_same_predecessor`, `paper_good_minimal_pre`, `paper_core_minimal_pre`, `paper_core_bad_proportion`, and `paper_core_current_coherence` supply candidates for all the assertions of Lemma 8.4 on `ModeComponents`, under the component/stabilization hypotheses. In the last result the early common good height is obtained by counting a union of the actual paper bad-height sets, not assumed.

## Lemma 8.10

`typed_representatives_paper` adapts the attributed reference proof to the exact printed primary and mode types and the printed good predicate. It returns representatives in the PRE predecessor, consistent inheritance, disjoint distinct predecessors, and later CURRENT nonadjacency. The input remains the actual frozen reference `ModeSystem`; existence of a full paper-good successful-node catalog and its connection to later first-top/counted-tuple constructions are not proved here. The final frequency inequality (25) follows on the reference data from `Auto.ModeSystem.alive_representative_separation` with its existing radius and curvature assumptions; the full use-cell correspondence remains open.

## Sections 9 and 10

`paper_common_height` obtains a common success probability >= 1-2*m0*delta and a normalized geometric first-success series, using the paper-specific core definitions. It does not construct the complete role-mask expansion. `paper_side_pure_gap` applies the actual reference annulus exclusion under the stronger printed predicate, retaining its schedule and shift-height assumptions. `paper_type_mem`, `paper_type_range_le`, and `paper_top_test_card` supply the base-1.1 type range and joint height/type/amplitude-test count <= H^4. These do not establish the analytic first-top energy for the new type classes.

## Remaining work

- Section 2: exact original local kernel and outer reduction.
- Section 3: full compression correspondence and corrected-height integration.
- Section 4: exact LSS inverse theorem, pooled Fourier tails and correspondence.
- Section 5: actual delayed fits and adaptive schedules.
- Section 6: actual graph, masks and helper filters.
- Section 7: weighted maximal theorem and actual stack-energy budgets.
- Section 8: use the new printed predicates/types consistently throughout the actual reference side/core split, density chains, representative catalogs, first-top estimates and energy construction. The old downstream proof still uses its original reference predicates; it has not been silently relabeled.
- Section 9: complete selected-mode masks and original progression normalization/error budgets.
- Section 10: establish actual analytic reserves and integrate final parameter choice.

The printed Lemma 3.5(2) remains false without its correction. The exact LSS inverse theorem is not replaced by a different theorem. Whole-paper source remains incomplete. All new proofs require later elaboration/kernel checking by the user.
