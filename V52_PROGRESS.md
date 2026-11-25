# V52 — Nonfuture-pair mass, parameter ordering, and iterated Weyl samples

Source: `paper(6).pdf`, October 5, 2026 manuscript; exact SHA-256 match retained.

## New modules

### `OpenAI086/PaperV52SparseNonfuture.lean`

Formalizes the nonfuture-pair estimate in Lemma 9.1, p.84. For a fixed pair of roles and each counting block `b`, assume

- `0 ≤ mass b ≤ α M^2`,
- `mass b ≤ L * x b * y b`,
- `∑_b x b ≤ M` and `∑_b y b ≤ M`.

The Lean theorem derives

`∑_b mass b ≤ sqrt (L*α) * M^2`

using the pointwise product bound and finite Cauchy–Schwarz on `sqrt (x b)` and `sqrt (y b)`. A second theorem sums over a finite family of at most six role pairs, matching the six-pair assignment in the manuscript.

This does NOT prove the geometric hypotheses, nonfuture partition, greedy blocks, difference covers, slab covering, or the final `δ^(1/2080)` sparse-mass estimate.

### `OpenAI086/PaperV52ParameterOrder.lean`

Formalizes the numerical parameter choices in Section 10.3, p.92:

- choose `2 < q < 3` with `C19*C5*(q-2) < 1/8`;
- choose `α > 0` with `α*C4 < ε/2`;
- derive the side-cost inequality `P^(-1/2) G0 (K+2)^β ≤ P^(-1/4)` under `G0 ≤ P^(1/8)`, `K+2 ≤ P`, and `β ≤ 1/8`;
- derive the powered main-term estimate from the explicit ceiling-power bound `P^C4 ≤ 2^C4 η^(-α*C4)`.

The proof that the analytic complexity quantities satisfy these size hypotheses, and the derivation of the ceiling-power bound from `P = ceil(η^(-α))`, remain separate obligations.

### `OpenAI086/PaperV52IteratedWeylSamples.lean`

Formalizes the repeated-translation step in Lemma 4.3, p.17. If every step is multiplication by a unit complex phase up to error `e`, the initial Fourier sample is at least `3δ/4`, and `M e ≤ δ/4`, then all samples through index `M` are at least `δ/2`. A bridge then supplies the repeated-sample hypothesis to the existing disjoint-ball Plancherel return theorem.

The chart-specific derivation of the one-step recurrence and its error from the paper's `F(z+h)` translation identity remains open.

## Verification

Static checks:
- 318 independent Lean files reachable; no missing imports or cycles.
- 59-result registry consistent.
- Exact Theorem 1.1 statement lock unchanged.
- No `sorry`, `admit`, custom axiom, or excluded upstream import detected.
- 3,000 exact/rational regression models passed (1,200 sparse-pair, 1,000 parameter, 800 Weyl-sample cases).

Kernel:
- Lean and Lake executables are absent in this runtime.
- V52 target verifier exits 2 and records all seven targets as blocked.
- No theorem is promoted to kernel-verified.

## Remaining major obligations

- Lemma 4.3: derive the chart-specific approximate Fourier recurrence; finish successive-minima transference, rational isotropic projection height, and effective quadratic bound.
- Theorem 4.7: the full Leng–Sah–Sawhney degree-two inverse theorem remains an external dependency; the paper does not prove it internally.
- Sections 5–6: predictor moment replacement, delayed projections, full curvature graph/color/mask localization and quantitative error budgets.
- Lemma 7.2: full randomization fourth moment, leaf-depth rectangle partition, sampling errors, clipping and mixed-norm short-block comparison.
- Proposition 8.9: PRE graph, chain-length, Bessel row, leakage and offset-averaging derivations.
- Lemma 9.1: geometric difference-cover/slab argument and the positive `δ^(1/2080)` saving; V52 only closes the nonfuture-pair summation component.
- Proposition 2.3: derive all retained-cell analytic estimates and restart hypotheses from Sections 3–9, then combine with the parameter and tail estimates.
- Theorem 1.1: unconditional Schwartz trilinear estimate and unique bounded extension.

Current certification: 0/58 numbered mathematical results fully kernel-certified; Theorem 1.1 unproved.
