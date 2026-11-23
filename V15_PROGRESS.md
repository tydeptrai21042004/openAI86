# V15 continuation — real dyadic projection blocks and noncommuting rows

**Source:** `paper(4).pdf`, Lemma 3.3 (pages 8–9; the document's Oct. 5, 2026 revision).  This is an **independent source-level formalization candidate**. The Lean kernel has **not** checked it: `lean`/`lake` are absent and the environment cannot resolve the Lean distribution host.

## Mathematical progress

The paper fixes increments `Δ₀=P₀`, `Δₙ=Pₙ-Pₙ₋₁` for `n≥1` and then sums dyadic index blocks. The initial term must not be lost by treating the family as ordinary differences beginning at `P₀`.

Define `P̂₀=0` and `P̂ₙ₊₁=Pₙ`. For any width `w` and block `b`,

```text
Q_(w,b) = ∑_(j=bw)^((b+1)w-1) Δ_j
        = P̂_((b+1)w) - P̂_(bw).
```

Self-adjointness, idempotence, and nestedness pass from `P` to `P̂`. Consequently, for any vector `x` and finite number of blocks `K`,

```text
∑_(b<K) ||Q_(w,b)x||²
 = ||P̂_(Kw)x||² - ||P̂_0 x||²
 ≤ ||x||².
```

This bound is **unconditional under the actual nested projection hypotheses** and independent of `w`, `K`, and the largest depth.

If `B_r` is a row-Bessel family and every row independently selects a block index `b_r`, the already-proved adaptive-row lemma yields

```text
∑_r |B_r(Q_(w,b_r)x)|² ≤ ||x||².
```

The same remains true for **any ordered noncommuting product** of layers `Q_(i,w_i,b_(i,r))`, with independently selected widths `w_i` and row block indices `b_(i,r)`. If there are `K` different width tuples, finite Cauchy–Schwarz gives a squared-energy factor `K²`. This version is now stated for actual projection blocks instead of abstract `hblock` assumptions.

### Added modules

1. `OpenAI086/AugmentedNestedProjectionBlocks.lean` — zero-prepended family, self-adjointness/idempotence/nestedness preservation, initial-block identity and sharp aligned-block Bessel bound.
2. `OpenAI086/FiniteLinearProjectionBlockBridge.lean` — operator-level telescoping for *all* linear dyadic blocks and an exact identification with those projections; inherits Bessel without an independent energy hypothesis.
3. `OpenAI086/ActualDyadicTupleBessel.lean` — arbitrary row-dependent choices and noncommuting projection layers, with each layer having its own width.
4. `OpenAI086/ActualDyadicLevelSum.lean` — actual-projection multilevel energy assembly and a **linear** row-prefix reduction that takes an exact vector decomposition as a named hypothesis.

Each module is imported by `OpenAI086.lean`; the root `OpenAI086Whole.lean` import audit remains intact. Theorem declarations are **uncompiled Lean candidates**, not certified results.

## Remaining mathematical obligations — do not misreport as solved

- Construct a **uniform level-tuple indexing** for every *row-selected* dyadic prefix, showing that each ordered product equals a sum of at most `L_T^m` block words with the level choices aligned to the same dyadic grid. The existing linear dyadic prefix theorem proves each layer's algebraic identity; the new V15 energy theorem proves the Bessel part; the connection has not yet been formalized with a common finite tuple type. This missing hypothesis is named `hvector` (and `hdecomp` in the scalar reduction), not an axiom.
- Derive the **square-variation inequality** of full Lemma 3.3 for general `m` from the completed row-prefix theorem; previous V8 proves only endpoint/weak cases.
- Prove full Lemma 3.4 compression (including its quantitative constants); Sections 4–10 and Theorem 1.1 remain open. There are **0/59 fully Lean-kernel-certified manuscript results** in this independent repository.
- Compile and audit the new and prior V9–V14 candidates under the pinned Lean/Mathlib revision; static checks and Fraction matrix tests do not imply that Lean elaboration succeeds.

## Verification actually completed

`tools/test_v15_actual_projection_blocks.py`: 27,079 deterministic exact-Fraction checks of distinct rational orthogonal projections, genuine noncommuting layers, `P₀` initial-block inclusion, fixed-width telescoping, dyadic prefix decomposition, row-dependent prefixes, multilevel sums and ordered products. The **full ordered-product expansion** was tested numerically but is *not* yet a Lean theorem connecting the level tuples to the target.

All V14–V9 exact-arithmetic regressions and the errata regression pass. Static import reachability, result inventory, target inventory, and `sorry`/`admit`/`axiom`/`unsafe` source audits pass. None are a kernel certificate.

## Reproduce on Linux/WSL

```bash
unzip openAI86_V15_Independent_Continuation_FULL.zip
cd openAI86-main
bash verify_smoke_v15.sh
```

The script exits `2` after passing source/numerical tests when Lean/Lake are unavailable. To check the kernel separately after installing the **pinned** Lean version and Mathlib cache:

```bash
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
```

Any compilation failure means V15 and/or earlier candidates require repair; do not convert a failed build to a claim that a manuscript lemma is proved.
