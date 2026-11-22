## V7 — 22 November 2026 (current status)

- **59/59** indexed results have Lean entrypoints; **21/59** have source-related finite proof components; **38/59** have typed finite proxies only. **0/59** have full independently kernel-certified manuscript proofs.
- New: exact operator-level dyadic prefix and ordered-product expansion **without assuming commutativity** (`FiniteLinearDyadicExpansion`, `FiniteOrderedProductExpansion`, `FiniteDyadicNoncommutingBridge`); finite quantitative catalog bounds and four-slot increment expansions.
- **33,475 new exact-integer model tests PASS;** previous V5/V6 focused regression PASS. **No Lean kernel build** in this environment (`lake` missing), so even the newly authored Lean proof scripts remain unverified candidates.
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
five new independently authored partial mathematical components, including
a real finite-dimensional m=1 nested projection square-variation bound.
They are **not yet checked by Lean kernel** here; Theorem 1.1 is unproved.

### Continuation V3 (22 November 2026)

See [`CONTINUATION_V3_2026_11_22.md`](CONTINUATION_V3_2026_11_22.md).
Six new modules advance finite private-Gram bounds (§3.2), nested projection
orthogonality and multilevel/noncommuting Bessel inequalities (§3.3), and
weighted four-step walk counting (§9.3). The model tests cover 82,352
cases. **No Lean kernel build was run in the authoring environment.**
The theorem inventory remains 17/59 partial, 0/59 fully certified.
