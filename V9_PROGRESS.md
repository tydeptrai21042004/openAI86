# Independent Lean continuation V9 — 2026-11-22

**Source:** `paper(4).pdf`, 93 pages, `An L³ Bound for the Trilinear Hilbert Transform`.

## New mathematics and proof interfaces

1. `OpenAI086/HeightLagTelescoping.lean` supplies an **exact general finite-sum identity**
   `∑_{h < H}(p(h+Δ)-p(h)) = ∑_{r < Δ}(p(H+r)-p(r))` and its `≤ Δ L`
   consequence. This is the previously unformalized *height-lag* part of
   the count in manuscript Lemma 8.6, page 70.
2. `OpenAI086/HeightLagChainBridge.lean` combines that exact identity with
   existing two-way incidence and absorption lemmas. Unlike the earlier
   bridge, it does not assume a per-position Q budget; it derives it from
   the actual lagged differences plus a separately stated exceptional-height budget.
   The per-height **cross-position/entry-rank** hypothesis remains **open**.
3. `OpenAI086/FinitePredictorOrthogonality.lean` proves a weighted-cell
   version of the corrected Lemma 5.3 predictor identity, retaining
   `-√ε·(weighted private-input average)`. It is an algebraic step, **not**
   the full analytical predictor estimate (7).
4. `OpenAI086/FiniteLemma33Target.lean`: the row operators `B` in the
   explicit finite-real logarithmic goal have been corrected to **linear maps**.
   The previous arbitrary-function statement is mathematically invalid:
   `tools/test_v9_height_lag.py` exhibits a finite-dimensional counterexample
   to its claimed logarithmic estimate. Other analytic hypotheses and the
   m≥1 variable-prefix bound remain open.

## Repository and verification repairs

- Move the derivative/reference-authored `Lemma33Reviewed.lean` and
  `Lemma33Check.lean` into `verification/reference_only/`. These files
  are **not imported**, are **not counted** as independent results, and are
  preserved only for provenance under the bundled Apache license.
- All independent `OpenAI086` modules now reachable from `OpenAI086Whole`.
- Update the live metadata counts from source, fix PDF hash check to accept
  the uploaded `paper(4).pdf` with its already indexed SHA-256.
- Add `.github/workflows/lean-kernel.yml` for Linux kernel build and axiom
  inspection. This workflow is **not** evidence of having passed here.
- Add `verify_smoke_v9.sh` and 6,301 exact integer/rational arithmetic checks.

## Explicit limits

**This environment does not provide `lean`, `lake`, or `elan`, and external
network access is unavailable. NO Lean kernel build was performed.**
All newly authored Lean theorems are *uncompiled proof candidates*.
Static safety/import and Python numerical tests do NOT certify Lean proofs.

In particular, the full Lemmas 3.3, 3.4, 5.3, 8.6, 9.1,
Proposition 2.3, Theorem 2.2 and **Theorem 1.1 remain OPEN** in this repo.
The paper result inventory is still 21/59 with a partial source-related
component, 38/59 finite proxy only, and 0/59 fully certified results.

## Ubuntu verification

```bash
# Install elan with the repository pinned version of Lean, then:
./verify_smoke_v9.sh
# or run every regression:
./verify_all.sh
```

Both scripts intentionally exit with code 2 if `lake` is missing. Once
Lean is available, source compilation failures must be fixed rather than
reclassified as complete proofs.
