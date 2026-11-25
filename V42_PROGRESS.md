# V42 — complex private-column bounds, actual height obstruction, accuracy tail

**This release remains partial source formalization, not a complete proof.**
The source manuscript is the same 93-page October 5, 2026 PDF as V41.

## New mathematical proof candidates

- `PaperV42PrivateColumns.lean`: an explicit complex Hilbert-coordinate norm
  (not the default function sup norm), exact synthesis energy, injectivity of
  the private-coordinate synthesis, two-sided coefficient bounds, a derived
  complex pairing bound, and the normalized `D^5` refit estimate from the
  integrated orthogonality identity. The existence of the actual L² closed
  span projection, its moment identities, and almost-everywhere versions
  remain to be supplied. These are meaningful pieces of Lemma 3.2/3.4,
  not certification of either whole lemma.
- `PaperV42HeightCounterexample.lean`: witnesses height-two unit coefficient
  vectors in the actual `v34HeightValue` predicate, connects the two log
  windows to `v36Qualifying`, and derives the obstruction for any fixed
  additive integer bound K. This links the prior negative example to the
  actual evaluation set, rather than simply asserting an abstract window
  count. Keep the corrected statement and audit its downstream uses.
- `PaperV42AccuracyTail.lean`: constructs k_(n+1)=k_n^A for A≥2, derives
  quadratic growth, proves summability and an arbitrary small bound for
  the shifted weighted series (n+m) exp(-c*k_n^theta), and constructs a
  sufficiently large starting value above any given K. Take m=12 for
  the summation index in Section 10.4 (with k_12 as the starting value).
  This closes a source-level summation candidate, not the retained-cell
  analytic bound or Proposition 2.3.

## Verification

- 290 independent source files including the two entrypoints; all reachable.
- 838 line-anchored theorem declarations (16 added); source lexer count
  837 because it excludes commented declarations. Neither is a proof count.
- 59 indexed manuscript items; 59 partial, zero kernel-certified.
- All six static checks in `verify_v42.sh` pass; 1,350 exact finite model
  checks and 16 high-precision finite-tail checks pass.
- Lean and Lake unavailable. The verifier exits 2 with NOT RUN, not a pass.
  The new Lean proofs are uncompiled candidates; tactic/API errors may remain.
- Earlier V41 logs are retained as historical evidence, not rerun certificates.

## Still open (not silently assumed)

1. Complete a pinned Lean kernel build and repair elaboration errors.
2. Construct actual normalized-cell L² spans, orthogonal refits and almost-
   everywhere coefficient estimates; assemble full Lemma 3.4, including the
   stopping and restart constructions. Certify all of Section 3.
3. Complete local absolute estimate, optimal constant and maximal stopping,
   kernel reconstruction, outer reduction (Section 2).
4. Full quantitative Weyl theorem, external general quantitative U³ inverse,
   nilmanifold-to-chart transfer and local detection (Section 4).
5. Actual staggered approximation, finite predictor and adaptive stopping
   outputs; localization, color/history catalogs, complementary transfer
   (Sections 5–6).
6. Weighted mixed-norm maximal estimate and short-block comparison, with
   the correct q-dependent exponent; actual square-energy certificate and
   side estimate (Sections 7–8).
7. Sparse-count positive-power saving from the progression hypotheses, and
   core-power bounds (Section 9).
8. Noncircular full parameter hierarchy, retained-cell bound, normalized
   absorption, and the unconditional main analytic inequality (Section 10).
9. Final kernel-certified Theorem 1.1 and unique bounded extension; certify
   external dependencies and all 58 numbered results, and check Definition
   4.1 against the manuscript. No completion claim until these gates pass.

## Commands

On Ubuntu/WSL with the pinned toolchain installed:

```sh
bash verify_v42.sh
bash verify_paper_complete.sh
```

The second remains fail-closed. No new custom axioms or proof placeholders
were introduced. There is no claim that the whole paper is proved.
