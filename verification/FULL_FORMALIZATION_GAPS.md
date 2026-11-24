## V28 current status

V28: 58 partial source entries, one open external inverse theorem with discrete normalization infrastructure, 0 fully kernel-certified. Four new modules, 19 new theorem declarations; all new proofs are uncompiled candidates. See `V28_PROGRESS.md`, `V28_REMAINING_59.md` and `bash verify_smoke_v28.sh`. Earlier entries below are historical.

## V27 current status — 24 November 2026

253 reachable Lean files; 654 theorem declarations; 58 partial source entries, 1 open entry with proxy and domain definitions, 0 fully kernel-certified. 11,082 exact model checks passed. Theorem 4.7, uniform L³ estimate and Lean kernel verification remain open. See `V27_PROGRESS.md` and `bash verify_smoke_v27.sh`. Older statuses below are historical.

## V26 current status — 24 November 2026

245 reachable Lean files; 636 theorem declarations; 51 partial source entries, 8 proxy-only, 0 fully kernel-certified. 9,883 exact model checks passed. New direct components for 4.6, 4.10, 4.11, 4.12, 5.4, 5.6, 5.8, 6.3, 7.4. Lean/Lake unavailable; Theorem 1.1 and 4.7 remain open. See `V26_PROGRESS.md` and `bash verify_smoke_v26.sh`. Older statuses below are historical.

# Current V24 remaining gaps

21 proxy-only entries: Lemma 4.3, Lemma 4.4, Lemma 4.6, Theorem 4.7, Lemma 4.9, Lemma 4.10, Lemma 4.11, Lemma 4.12, Lemma 5.1, Corollary 5.2, Lemma 5.4, Proposition 5.6, Lemma 5.7, Proposition 5.8, Lemma 6.1, Lemma 6.3, Lemma 6.6, Proposition 6.8, Lemma 7.1, Lemma 7.2, Lemma 7.4.

38 entries have partial source components only; none of the 59 is fully independently kernel verified. The bounded extension and exact PV realization interface now exist as Lean candidates, but the actual Schwartz operator, analytic estimate, and kernel checks remain open. See `V24_PROGRESS.md`. Historical gaps follow.

# Complete paper obligations — detailed inventory

The canonical register is `PAPER_RESULTS_INDEX.md` / `.json`, generated from the user's 93-page `paper(1).pdf` and containing 59 numbered mathematical assertions/definitions with PDF page references.

## Dependency spine

Theorem 1.1 (principal-value L³ bound and extension) — OPEN
  ← Lemma 2.4 (outer reduction) — OPEN
  ← Theorem 2.2 (uniform local bound) — OPEN
  ← Proposition 2.3 (normalized absorption) — OPEN
  ← Sections 3–9 (projection, chart, localization, side/core count) — OPEN
  ← Section 10 (parameter choices and completion) — OPEN

Subcomponents proved **in authored source** include the arbitrary-depth noncommuting telescoping algebra, the four-family finite stopping-set bound, the `D³` path-label energy estimate, and the `d=0` quadratic chart calculus. Full paper statements are not proved by those restricted lemmas.

## Known mathematical text issues requiring explicit treatment

1. Lemma 5.3 predictor moment: include input private-coordinate terms (unless they are zero).
2. Lemma 8.6: verify the terminal inclusion at index `N`; early-index inclusions alone do not suffice.
3. Section 9.1 first failing role: preceding roles pass; later roles are unrestricted.

## Compile requirement

No successful Lake build was possible in the authoring runtime. The independent project intentionally excludes the published third-party formalization; its own main theorem therefore requires development of the analytic proof, not a wrapper or `axiom`.
