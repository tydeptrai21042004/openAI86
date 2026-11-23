# V17 — bounded dyadic selectors and a one-layer logarithmic prefix target

**Date:** 23 November 2026  
**Input:** `openAI86_V16_Independent_Continuation_FULL.zip`  
**Reference:** `paper(4).pdf`, Lemma 3.3, pages 8–9  
**Verification state:** no Lean kernel compilation performed. All new Lean source is **proof-candidate code**.

## Mathematical result pursued

For genuine nested self-adjoint idempotents `P n` acting on the real
finite-dimensional Euclidean space `Fin d → ℝ`, and a finite Bessel family
of **linear** scalar rows `B r`, row-dependent indices `N r < 2^k`
should satisfy

```
∑ r, (B r (P (N r) x))² ≤ (k+1)² ‖x‖².
```

This is exactly the one-family `m=1` finite-real specialization of the
first inequality in manuscript Lemma 3.3. It is **not** the arbitrary
Hilbert-space or noncommuting multi-family version. The `m=1` square-
variation endpoint is separately developed elsewhere in the repository.

## Source additions (5 files)

1. `FiniteDyadicBlockIndexBounds.lean` — proofs that every prefix block
   remains inside its requested interval, has strictly bounded starting
   position, and has bounded aligned index `b < 2^k`. The old `Nat`
   selector is thereby converted to a genuinely finite index.
2. `FiniteDyadicBoundedRowSelection.lean` — extracts `Bool` zero masks
   and `Fin (2^k)` block indices **from the actual prefix**, simultaneously
   for all rows and layers. Neither mask nor index depends on the test
   vector; no `hdecomp` premise is introduced.
3. `ActualDyadicSelectedWidthBessel.lean` — fixed-width row-Bessel
   source theorem from the actual selectors and the V15 nested-projection
   block-energy theorem. Requires genuine **linear** row maps.
4. `ActualDyadicOneLayerPrefix.lean` — finite-width subtype enumeration,
   one-family full variable-prefix inequality with squared-logarithmic
   width cardinality, plus the explicit `(k+1)²` result.
5. `FiniteDyadicWidthTupleEnumeration.lean` — a list-based word
   enumeration and proposed exact ordered noncommuting product identity.
   This is the algebraic next step toward the `m>1` proof; it does **not**
   yet connect every word to the masked Bessel inequality. Its Lean
   elaboration is unverified and may require Mathlib API adjustments.

## Independent mathematical-model regressions

- `tools/test_v17_actual_selected_width.py` — **442,192** exact
  rational/integer checks passed in full mode; **82,750** passed in the
  default fast smoke mode. Covers every zero-based prefix through
  `2^8`, all possible block masks, bounded `Fin` indices, `P₀` inclusion,
  fixed-width Bessel for independently varying row depths, the full
  one-layer logarithmic inequality, and up to four ordered noncommuting
  layers. Also verifies width-tuple enumeration cardinalities.
- `tools/test_v16_width_grouping.py` — **16,868** exact-rational
  regression checks passed independently, unchanged from V16. It is
  included in the optional `V17_EXTENDED=1` suite.
- Source import-reachability, 59-target inventory, and lexical safety
  audits pass. **None of these checks typecheck Lean proof terms.**

## Actual Lean verification gate

Run from the extracted root:

```bash
bash verify_smoke_v17.sh
# Optional slower full regression suites:
V17_EXTENDED=1 bash verify_smoke_v17.sh
```

- Exit **0** only after `lake build OpenAI086Whole` **and**
  `lake env lean OpenAI086Whole.lean` succeed.
- Exit **2** if source/model tests pass but the toolchain is absent.
- Other nonzero exit indicates audit, test, or compilation failure.

This environment has neither `lean` nor `lake`, and cannot resolve the
Lean download hosts. Do not mark any new declaration kernel verified.
The historical registry remains **21/59 partial**, **38/59 proxy only**,
**0/59 fully manuscript-equivalent and kernel certified**.

## Still open / next mathematical work

1. Kernel compile the independent source and fix elaboration failures
   (including any in earlier V9–V16 modules).
2. Reindex `enumerateWidthTuples` as one finite type of width tuples,
   with cardinality at most `(k+1)^m`, and connect the tuple masks and
   bounded `Fin` indices to `actual_dyadic_masked_multilevel_bessel`.
3. Derive arbitrary `m` variable-prefix and square-variation estimates,
   then extend finite-real statements to arbitrary complex Hilbert spaces.
4. Prove Lemma 3.4 compression and the remaining analytic Sections 4–10.
5. Certify the exact principal-value operator and Theorem 1.1; **still open**.

The project is intentionally independent of the published formalization.
