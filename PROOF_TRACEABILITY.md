# Exact traceability register

The canonical result-by-result index is `verification/PAPER_RESULTS_INDEX.md` and `.json`. All 59 numbered results of the October 5, 2026 PDF are indexed by exact physical page number and corresponding local partial components, when available.

The main target is **only declared** in `OpenAI086/PaperStatement.lean` and is not proved.

Seven independently authored proof-component files are imported into `OpenAI086.lean`:

- `ArbitraryDepthTelescoping.lean` — arbitrary-depth ordered algebra (noncommuting)
- `OrderedProductTelescoping.lean` — explicit 3/4 layer expansions
- `FiniteStoppingSets.lean` — four-family finite stopping cardinality
- `FiniteMarginalCancellation.lean` — discrete marginal telescoping
- `PathLabelEnergy.lean` — finite label energy bound
- `QuadraticChartsElementary.lean` — ordinary quadratic chart calculus
- `EntryRankSummation.lean` — harmonic entry-rank budget summation

These are **not** replacements for full Lemma 2.4, Lemma 3.3, Lemma 3.4, Lemma 4.2, Lemma 8.5, or the full analytic arguments in the paper. The project has not been compiled with Lean in the authoring runtime.

## Additional sections 8--9 coverage (continuation)

- `ComponentIntersections.lean` — quantitative predecessor overlap in Lemma 8.10.
- `EntryRankConcrete.lean` — entry-rank denominator control and harmonic incidence in Lemma 8.5.
- `SparsePairBudget.lean` — incidence mass `≤ L M²` in Lemma 9.1.
- `SparseBlockAccounting.lean` — conditional greedy block-count arithmetic in Lemma 9.1.
- `ColoredPathUniqueness.lean` — proper edge colors uniquely determine a four-step path.

All source statements are uncompiled candidates until the pinned Lean toolchain is run.
