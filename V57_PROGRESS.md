# V57 — paper-faithful continuation

V57 continues V56 and preserves the exact main theorem statement. The original 93-page paper has SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`; `paper(9).pdf` and `paper(7).pdf` match exactly.

## Mathematical source changes

1. **Lemma 8.2 (second assertion), pp. 67–68.** `source_fidelity/v57/TinySpan.lean` is an isolated, attributed adaptation of Joris Roos's Apache-2.0 reference source, including the rational-height dependence prerequisite. The proof selects an independent subfamily of size at most d, obtains a nonzero integer relation whose coefficient on the tested vector is nonzero, and uses the bound `d! H^(d²+d)` on the coefficients. It yields `|a·Θ| ≤ d (d! H^(d²+d)) ε` for a height-H vector in the span of tiny vectors, so a sufficiently wide tiny/large gap forces it to be tiny. Unlike the reference's enumeration-size reserve, this candidate uses the dimension factor alone. It also derives the reserve from `d (d! H^(d²+d)) < T²` and `0 < r_t ≤ r_v`, with thresholds `ε=1/(T r_v)` and `Λ=T/r_t`. The first assertion has the V56 five-start count. The two sources still need kernel verification and a statement-equivalence review on the concrete block data.
2. **Lemma 8.6, pp. 69–70.** Extended the isolated V56 adapted entry-rank file with a proof candidate using the actual floor of log base 1.1, the initial bad heights, exact harmonic coefficient, strict bad-height density and union-of-exceptions predicate. It derives fractional incidence budgets directly from per-label occurrence bounds using the first-entry proof. The terminal inclusion `P_N,h ⊆ C_N,h` is explicit because the printed chain hypothesis only quantifies `i<N`. The candidate therefore proves the corrected chain, not the printed lemma with that missing endpoint. The original application must establish this terminal inclusion. Infinite indexing is just a convenience; the finite families can be extended constantly past their last stages, with empty bad sets after the horizon. `Y` is assumed to contain only height-bad nonexceptional labels, or equivalently restrict it to nonexceptional labels before the call.
3. **Section 10.4, p. 93.** `OpenAI086/PaperV57BaseSummation.lean` is new independent code. It sums per-tuple cost bounds using the O(t) number of tuples and the V42 weighted accuracy series, obtains one starting accuracy uniform over finite cutoffs, and passes a uniform real bound to an existing limit. Analytic per-tuple estimates, construction of the segment packing constant and actual staggered expansion convergence remain hypotheses. It is not a proof of Proposition 2.3.

## Lemma 3.5(2) downstream paper audit

The corrected scale count adds the dimension factor to the bandwidth term. The explicit height-bin uses in the manuscript are as follows:

| Page / section | Application | Effect of correction |
|---|---|---|
| 30–31, Lemma 5.1 | Exceptional intermediate annuli | dimension, log catalog height and log annulus width are all polynomial in K; the extra dimension factor is absorbed by increasing the polynomial degree. |
| 30–31, Lemma 5.1 | Tiny-scale sum and Bessel shell counting | tiny sum uses part (3), not the erroneous part (2); fixed shell count uses an annulus of bounded log width. |
| 37–38, Lemma 5.7 | Triple-norm intermediate-scale count | dimension and log height are controlled by the stated quasipolynomial budgets; the correction preserves polynomial log-budget dependence. |
| 67–68, Lemma 8.2 | K-spaced exceptional blocks | uses part (1), the packet-width cover; no bandwidth correction needed. |
| 87–88, Proposition 9.2 | Pair-fixed scale occurrences | the extra dimension factor is absorbed in the polynomial in P and `1+log(ν/μ)` because dimension is polynomially bounded. |

This is a mathematical source audit of the explicit uses, not a formal proof of all downstream applications or implicit uses. Original statement (2) stays refuted; the corrected candidate stays marked partial.

## Verification

`bash verify_v57.sh` checks import reachability, source lock, registry, original PDF identity, lexical source safety (including the isolated adapted files) and 1,180 deterministic exact rational models. The latter cover 180 tiny-span models, 500 chain models, 500 tuple cutoffs. These are regression tests, not Lean proofs. Then the verifier tries the isolated adapted files and independent whole-project build and checks exact axiom reports for named declarations. In the authoring environment `lean` and `lake` are absent, so it exits 2, with zero kernel-verified results. No proof placeholder or custom axiom is introduced in the new source. The reference-derived source is kept outside the independent import tree and is not counted as independent authorship.

## Remaining

The exact full manuscript is not yet formalized. Still open: proof replay; exact projection compression; chart and detection analytic arguments; the precise external LSS theorem (the finite inverse result in the reference is an alternative); complete adaptive approximation/localization; short-block torus estimate; graph and Bessel-row energy; geometric sparse counting; full base-expansion analytic convergence; and the independent normalized absorption and main theorem. The V55 external proof bridge is retained but is not a certificate for these intermediate statements. The 58 mathematical certificates are all still open.
