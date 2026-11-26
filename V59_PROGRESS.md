# V59 — paper fidelity and concrete analytic candidates

Base: V58. Original manuscript SHA-256: `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`.
The independent tree, locked main statement, and 59-entry paper registry are unchanged. No paper result is promoted to certified; Lean and Lake are unavailable in the authoring environment.

## Important correction to the V56–V58 fidelity audit

Visual inspection of the actual equation on printed page 10 confirms that Lemma 3.4 states

`(sum rows squared)^(1/2) <= (C (m+1)^C log(2D))^(C(m+1)) ||z||_2`.

The outer exponent applies to the **whole parenthesized factor**. Earlier notes incorrectly attached it only to the logarithm. The reference's `columnSpatialCompression` (C=512) and `columnSpatialCompression_complements` (C=1024) therefore have the required growth. This supersedes the quantitative-mismatch claim in earlier progress reports. The reference's own detailed proof uses the size segments, moment representatives, anchor stopping and length/energy contraction of the paper.

## Lemma 3.4 (pp. 9–13)

`external_main_theorem/v59/Compression.lean`:
* `ae_halfopen_overlap` and `ae_dyadic_path_count`: a finite half-open interval system with a.e. bounded overlap has pointwise bounded overlap. For a fixed point, the minimum of the right endpoints of all intervals containing it is strictly larger than the point. On the resulting nonempty half-open interval every originally present label remains present. A violation would thus occur on a set of positive measure.
* `rowSingle` is the isometric injection into a finite Hilbert direct sum, adapted from the reference's `piLpSingle` in `Sec13_3BesselRowsLinearSideEnergy.lean`. `dependentRows` builds the actual common-codomain row family while preserving the squared row norm, Bessel bound, and support-locality identity.
* `lemma34_projections` and `lemma34_complements` use the reference's actual spatial compression theorem and derive the square-root sum with different row Hilbert codomains and the printed quantitative form. The source candidates use the reference's concrete `ColumnTreeData`, `InheritedColumnMask`, and global zero-extension L² representation, not the independent finite proxy.

Remaining: kernel replay; explicitly assemble the manuscript's interval-domain data (including root restriction of the a.e. assumption) into the reference data; handle the finite-measure average clause and all statement correspondence. The new a.e. overlap theorem is a separate construction tool; the compression declarations still take a completed reference tree. Independent Lemma 3.4 remains open.

## Lemma 4.3 (pp. 16–18)

`external_main_theorem/v59/Weyl.lean` contains `lemma43`, an explicit reference-backed analytic Weyl statement with the actual chart, two rational projection matrices, isotropy, bounded matrix heights and bounded slow/effective quadratic norms. For 0 < delta < 1/2, the reference's log(max(1,1/delta)) is exactly log(1/delta). It invokes the complete reference Weyl proof (`Sec09_1ReturnWeylSplitting.lean`), not a supplied splitting hypothesis. Remaining: kernel replay and chart complexity/norm convention correspondence. The reference's geometry-of-numbers argument uses an adapted transference constant; the original step-by-step proof is not reconstructed independently.

## Lemma 7.2 (pp. 53–57)

`source_fidelity/v58/ShortBlockGeometry.lean` adds attributed actual finite rectangle definitions, exact partition of unity, selection of distinct designated slots, heavy/regular depth bounds, and both designated mask disjointness results within one level. Extracted from the reference `Sec14_2aShortBlockSampling.lean` (heavy/designated/level definitions, lines 1899–1940) and `Sec14_2bShortBlockSummation.lean` (Side/upTo/partition, lines 1068–1140; designated bounds and disjointness, lines 3785–3872). These are additions to the existing V58 Mathlib-only isolated source; the original copyright header is retained.

`source_fidelity/v59/RadialClipping.lean` independently derives the original paper's radial clipping inequality. For positive A, define the clipped complex number by leaving it unchanged inside the radius-A ball and scaling by A/|z| outside. The exact norm loss is max(0,|z|-A), bounded by |z|²/A. The integral theorem derives integrability of the error and the L¹ estimate using the square-integrability of the norm. This does not yet prove the entire randomized heavy-slot estimate.

`external_main_theorem/v59/ShortBlock.lean` gives `lemma72`, a reference-backed full short-block comparison candidate on the actual reference tree/kernel data. It uses the reference's stronger exponent `2(q-2)/(q-1)` and weakens it to `2(q-2)` for `2<q<3`, with the logarithmic and uniform finite-depth factors preserved. The reference requires fourth pointwise moments only and uses a different heavy-slot argument, rather than the original manuscript's full clipping/interpolation route. Exact tree/kernel correspondence and kernel replay remain necessary; the manuscript proof is not independently complete.

## Verification

* `bash verify_v59.sh`: static audits and 5,998 deterministic exact regression model cases (600 half-open families, 600 radial clips, 4096 depth tuples, 202 rectangle levels/positions, 500 exponent comparisons). These test arithmetic/finite constructions, not Lean proof terms. It then checks exact axiom reports for the isolated files; it exits 2 when Lean/Lake are absent.
* `python3 external_main_theorem/v59/verify_bridges.py <reference ZIP> --work-dir <new empty directory>`: validates pinned archive identity and locked statement, builds the required reference modules and audits the exact bridge declarations. `--target Compression`, `--target Weyl`, `--target ShortBlock` choose a subset. `--prepare-only` prepares without certifying. Certificates distinguish dependency-backed proof from independent completion.
* Prior V58 sparse-count verifier and V55 main theorem verifier remain available and separate.

## Remaining obligations

- All existing proof candidates, including Lemmas 3.1, 3.2, 3.3, corrected 3.5, 8.2, 8.5, 8.6: kernel replay and exact statement/application review.
- Lemmas 3.4, 4.3, 7.2 and 9.1: reference-backed proof candidates are not yet kernel checked. Complete data correspondence; for Lemma 3.4 also the averaging clause; for a fully independent proof, reconstruct all mathematical steps.
- Theorem 4.7: exact Leng–Sah–Sawhney external theorem, not the reference's alternative finite inverse theorem.
- Sections 5–6 and 8: actual adaptive approximations, localization, graph energy and leakage; no new result promoted.
- Sections 9–10: apply sparse count to actual tests, complete core estimate, quantitative hierarchy, analytic expansion convergence and normalized absorption.
- Proposition 2.3, Theorem 2.2 and Theorem 1.1: independent proof still open. V55 reference-backed main theorem bridge is separate and remains unverified here.
