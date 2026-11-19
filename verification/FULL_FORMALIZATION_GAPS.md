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
