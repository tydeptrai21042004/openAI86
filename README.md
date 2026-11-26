> V61 continuation: see [V61_PROGRESS.md](V61_PROGRESS.md) and `verify_v61.sh`. New proof candidates have not been kernel-checked; the historical independent inventory remains unchanged.

# OpenAI086 — V60 consolidated Lean source

**Status: source release, not a completed or kernel-certified whole-paper proof.**

Start with [FINAL_SOURCE.md](FINAL_SOURCE.md). This release combines the latest independent partial formalization, the attributed standalone candidates, the V55–V60 reference-backed bridges, the original 93-page paper and the pinned reference archive. The final two theorem declarations are in `final_source/FinalMain.lean` (reference-backed, not independent). Run `bash verify_final.sh --main-only` for the main targets, or `bash verify_final.sh` for the broader replay. Older README sections below are historical.

> **V59 (historical):** [V59_PROGRESS.md](V59_PROGRESS.md). Corrected Lemma 3.4 exponent audit, reference-backed compression/Weyl/short-block candidates, radial clipping and rectangle separation. No kernel certification here. Run `bash verify_v59.sh`.

> **V58:** see [V58_PROGRESS.md](V58_PROGRESS.md). Source candidates for Lemma 7.2 and reference-backed Lemma 9.1; kernel certification not run. Independent main theorem remains open. Run `bash verify_v58.sh`.

> **V53 status:** source-level continuation only; whole Lean kernel build remains unverified. See [V53_PROGRESS.md](V53_PROGRESS.md) and run `bash verify_v53.sh`. Theorem 1.1 is still open.

> **V45 update:** See [V45_PROGRESS.md](V45_PROGRESS.md) for the scalar-input normal equation and continuous cut-refit candidates. Static checks passed; Lean kernel checks blocked (0/58 certified, 0/1 unconditional main theorem).

> **V43 continuation:** see [V43_PROGRESS.md](V43_PROGRESS.md). Run `bash verify_v43.sh` or the GitHub Actions workflow for isolated kernel checks. No manuscript result is certified here; the unconditional main theorem remains open.

# V41 — integrated independent Lean source project (PARTIAL)

Current status: **287 independent files, 822 line-anchored theorem declarations, 59 indexed partial items, 0 fully certified.** Imports and static metadata repaired. Lean/Lake unavailable here; no successful kernel build and no proof of Theorem 1.1. See [V41_PROGRESS.md](V41_PROGRESS.md). Run `bash verify_v41.sh` on the pinned toolchain. Older sections below are historical release notes, not current status.

---

## V17 continuation — 23 November 2026

New **uncompiled** Lean source targets bounded dyadic `Fin (2^k)` block
indices, automatically selected zero masks, and the **one-family**
finite-real logarithmic prefix estimate in Lemma 3.3. It also includes
a candidate explicit width-tuple enumeration for noncommuting layers.
The new exact-arithmetic model passes 442,192 checks. Source-model
checks are **not** a Lean-kernel certificate. Run
`bash verify_smoke_v17.sh` and read `V17_PROGRESS.md`.
**Theorem 1.1 remains open (0/59 full manuscript results certified).**

---

## V14 continuation — 23 November 2026

Six new **uncompiled Lean proof-candidate modules** connect the complete `H+lag` bad-height window and the strict quantitative conclusion in the finite Lemma 8.6 model; a separate module reformulates `L` binary-block Bessel levels with an `L²` squared-energy cost for Lemma 3.3, and the dyadic prefix is proved to have unique block widths and aligned starts. See [V14_PROGRESS.md](V14_PROGRESS.md) and run `bash verify_smoke_v14.sh`. **No Lean kernel certificate is available and Theorem 1.1 remains open.**

---

## V13 continuation — finite first-entry harmonic bound (22 November 2026)

Constructs chronological entry ranks from arbitrary nested finite sets, proves
finite permutation/rank-size and harmonic incidence proof **candidates**,
and applies independently ordered ranks to both counting axes in the
Lemma 8.6 shifted-window bridge. The initial bad-height regime is counted
separately. See [V13_PROGRESS.md](V13_PROGRESS.md) and run
`./verify_smoke_v13.sh`. **Kernel compilation has not been performed.**
**Theorem 1.1 is NOT proved here.**

---

## Continuation V9 — 22 November 2026 (latest)

- New independently written Lean proof candidates: `HeightLagTelescoping`,
  `HeightLagChainBridge`, `FinitePredictorOrthogonality` for Lemmas **8.6** and **5.3**.
- The finite row-prefix goal for **Lemma 3.3 now requires linear rows**; the old
  arbitrary-function signature was mathematically invalid.
- Structural import audit, 59-result bookkeeping, and 6,301 exact arithmetic
  V9 regression cases pass. **Lean kernel build NOT run here** (Lake absent).
- Theorem **1.1 remains OPEN**. See `V9_PROGRESS.md`; run `./verify_smoke_v9.sh`
  in Ubuntu/WSL with the pinned Lean toolchain.

---

## V7 — 22 November 2026 (current status)

- **59/59** indexed results have Lean entrypoints; **21/59** have source-related finite proof components; **38/59** have typed finite proxies only. **0/59** have full independently kernel-certified manuscript proofs.
- New: exact operator-level dyadic prefix and ordered-product expansion **without assuming commutativity** (`FiniteLinearDyadicExpansion`, `FiniteOrderedProductExpansion`, `FiniteDyadicNoncommutingBridge`); finite quantitative catalog bounds and four-slot increment expansions.
- **33,476 new exact-integer model tests PASS;** previous V5/V6 focused regression PASS. **No Lean kernel build** in this environment (`lake` missing), so even the newly authored Lean proof scripts remain unverified candidates.
- Start with `bash verify_smoke_v7.sh`; see `V7_PROOF_PROGRESS.md` and `ALL_59_LEAN_TARGETS.md`.

---

## November 22, 2026 — V6 status (not full formalization)

- **59/59** paper results now have Lean source entrypoints in a Lean catalog.
- **17** have partial source components and **42** only typed **finite proxy goals**.
- **0/59** have complete, kernel-certified manuscript proofs.
- New code: `FiniteDyadicOperatorBridge`, `FiniteLemma33Target`,
  `FiniteCatalogClosure`, `FiniteClippingBudget`, `FinitePathTelescoping`,
  `FiniteGowersCubePhase`, `FiniteFourLinearCauchy`.
- Start with `bash verify_smoke_v6.sh`; only a successful `lake build`
  can confirm proof-term typechecking. See `CONTINUATION_V6_2026_11_22.md`
  and `ALL_59_LEAN_TARGETS.md` for precise status and scope.

# OpenAI #086 — independent Lean 4 proof development (PARTIAL)

**No Lean-kernel certificate for the paper is included. Theorem 1.1 is not proved.**

The project provides independently authored, small and medium-size Lean components
for the 93-page manuscript *An L³ Bound for the Trilinear Hilbert Transform*.
The historical adapted Lemma 3.3 files have been deliberately excluded.
All listed proof declarations require an actual `lake build` before they can be
regarded as Lean-kernel-accepted.

## Build (Ubuntu/WSL)

```bash
python3 -m pip install numpy sympy
bash verify_all.sh
# Or use the Ubuntu/WSL helper (requires elan/Lake): bash verify_ubuntu.sh
```

Lean is pinned in `lean-toolchain`, and Mathlib is pinned in `lakefile.toml`.
GitHub Actions runs a real kernel build on push/pull request.
If `lake` is unavailable, `verify_all.sh` exits 2, not 0.

## New independent proof bridges

- `FiniteTonelliBudget`: finite weighted pathwise summation (§3.1).
- `FiniteMultifamilyStops`: arbitrary family stopping-union inequality (§§2–3).
- `ArbitraryColoredPaths`: arbitrary even-length alternating path colors (§9.1).
- `FirstFailureAnyRole`: arbitrary finite first-failure role selection (§9.1).
- `FiniteFirstSuccessWeights`: finite first-success identity and geometric history bounds (§9.1).
- `CompressionRowError`: finite coefficient-error/Bessel summation (§3.4),
  with Cauchy–Schwarz and Bessel explicitly stated as hypotheses.

These are **partial consequences**, not substitutes for the analytic and
combinatorial depth-uniform theorems. The manuscript obligation register is
`verification/PAPER_RESULTS_INDEX.md`. For Vietnamese notes see `README_VI.md`.


### Continuation v2 (22 November 2026)

See [`CONTINUATION_V2_2026_11_22.md`](CONTINUATION_V2_2026_11_22.md) for
six new independently authored partial mathematical components, including
a real finite-dimensional m=1 nested projection square-variation bound.
They are **not yet checked by Lean kernel** here; Theorem 1.1 is unproved.

### Continuation V3 (22 November 2026)

See [`CONTINUATION_V3_2026_11_22.md`](CONTINUATION_V3_2026_11_22.md).
Six new modules advance finite private-Gram bounds (§3.2), nested projection
orthogonality and multilevel/noncommuting Bessel inequalities (§3.3), and
weighted four-step walk counting (§9.3). The model tests cover 82,352
cases. **No Lean kernel build was run in the authoring environment.**
The theorem inventory remains 17/59 partial, 0/59 fully certified.


## V10 continuation (2026-11-22)

Five additional **uncompiled** Lean proof-candidate modules and 11,976 finite
regressions are documented in `V10_PROGRESS.md`. Use `./verify_smoke_v10.sh`
for source/numerical checks and a real Lean kernel build. The manuscript
Theorem 1.1 is **not** proved in this repository.

### V12 exact rank and bad-density continuation

See [`V12_PROGRESS.md`](V12_PROGRESS.md) for the four new Lean proof
candidate modules and the precise remaining assumptions. Run
`./verify_smoke_v12.sh`. Source/numeric PASS is **not** Lean kernel
certification; `lake build OpenAI086Whole` must succeed before any new
Lean theorem can be claimed verified.


## V15: actual dyadic Bessel blocks (uncompiled source candidates)

See [V15_PROGRESS.md](V15_PROGRESS.md). New modules connect the `Δ₀=P₀` convention to fixed-width projection blocks and prove candidate energy assemblies for row-dependent, potentially noncommuting layers. The full length-tuple decomposition for arbitrary row prefixes and Lean kernel compilation remain open. Run `bash verify_smoke_v15.sh`.


### V16 continuation (source candidates, not a kernel certificate)

Run `bash verify_smoke_v16.sh`. New math: exact row-dependent dyadic prefix grouping by common widths, zero-or-aligned-block extraction, and masked noncommuting Bessel row-energy candidate. See `V16_PROGRESS.md` for the exact remaining proof obligations.

## Latest continuation: V46

See [V46_PROGRESS.md](V46_PROGRESS.md). Run `bash verify_v46.sh` for the new candidate checks. The full paper remains uncertified.

## V49 continuation

V49 adds `PaperV49AnchorCoherence.lean` and `PaperV49ErrorRows.lean`.
The former proves that a current active-anchor cell determines its complete
selected-anchor history through that depth and its predecessor anchor label.
The latter formalizes the p.12 finite coefficient-error row estimate from
explicit row Bessel contraction and the integrated `D^3` column-energy
budget. These remain uncompiled Lean candidates; static audits and finite
exact-rational model checks are not kernel certificates. See
`V49_PROGRESS.md` and `V49_VERIFICATION_LOG.txt`.


## Latest continuation: V50

V50 adds `PaperV50StageProjectionBridge.lean`: actual continuous L² stage
spans from measurable local columns, nestedness from an explicit almost-everywhere
refinement identity, an application of Lemma 3.3 to those stage projections,
and coefficient-synthesis identities for consecutive ordered products. The
remaining geometric refinement and cross-atom support-orthogonality obligations
are explicit. Run `bash verify_v50.sh`; when Lean/Lake are unavailable, kernel
verification correctly reports `BLOCKED` rather than success. See `V50_PROGRESS.md`.


## Latest continuation: V54

See [V54_PROGRESS.md](V54_PROGRESS.md) for the new source-level candidates and remaining obligations. Run `bash verify_v54.sh`. Five modules advance actual stage refits, greedy sparse blocks, the finite resonant fourth moment, chart phase algebra and retained-cell parameter assembly. No full paper result has been certified; the Lean/Lake phase remains blocked in the authoring environment.
