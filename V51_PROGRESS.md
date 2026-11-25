# V51 — Weyl return algebra, external inverse input, staggered expansion, and square-energy assembly

Source basis: `paper(6).pdf`, October 5, 2026 manuscript. Relevant locations:

- Lemma 4.3, pp. 16–18: return-frequency constraints, integer skew obstruction, isotropic rational subspace.
- Theorem 4.7, p. 22: explicitly external Leng–Sah–Sawhney degree-two inverse theorem.
- Section 5, pp. 29–38: staggered approximants and increment expansions.
- Lemma 7.2, pp. 53–56: four-slot Fourier randomization and short-block comparison.
- Proposition 8.9, pp. 72–73: event rows, PRE-chain colouring, projection Bessel energy, and exact subtotal error.

## New modules

### `OpenAI086/PaperV51WeylReturnAlgebra.lean`

- Parametrizes the exact nullspace of the two progression constraints as
  `m_j = c_j (h + j h')`, `c=(-1,3,-3,1)`.
- Re-derives the quadratic randomizer phase cancellation and its complex exponential form.
- Proves that an integral skew pairing of short-return generators, bounded by `1/4`, vanishes on the generated real span. This is the exact integer-obstruction-to-isotropy bridge used in Lemma 4.3.
- Does not prove the chart-specific shift-error, Fourier Lipschitz, disjoint-ball Plancherel, rational successive-minima, or bounded-height projection estimates.

### `OpenAI086/PaperV51LSSExternalInterface.lean`

- Records the witness contract for Theorem 4.7, including a degree-two filtered nilmanifold marker, adapted-orbit marker, conjugated correlation, dimension bound, complexity bound, Lipschitz bound, and inverse-epsilon bound.
- The manuscript explicitly cites Leng–Sah–Sawhney as an external input. The interface is therefore a parameter `V51LSSExternalInput`; it is not a custom axiom and does not claim to construct the nilmanifold or prove the external theorem.
- The abstract carrier and certificate predicates are an interface boundary, not a concrete Lie-group/quotient formalization.

### `OpenAI086/PaperV51StaggeredExpansion.lean`

- Proves the exact four-slot product telescoping identity used in staggered-accuracy expansions.
- Derives the corresponding complex norm bound in terms of the four one-slot increments.
- Does not establish the Section 5 predictor moments, delayed-projection estimates, or Gevrey/Fourier tail bounds.

### `OpenAI086/PaperV51Prop89Assembly.lean`

- Combines event projection energy, exact-subtotal replacement error, and a per-colour near-orthogonality estimate.
- Derives the conditional bound `K * (2*(A+B)*|R|)`.
- The PRE graph, chain-length estimate, projection leakage, offset averaging, and actual event-to-colour construction remain analytic obligations.

## Exact regression checks

`tools/test_v51_components.py` passes 2,500 exact rational cases:

- 1,000 progression-frequency/nullspace and phase-cancellation models.
- 1,000 four-slot telescoping models.
- 500 colour-partition energy identities.

These are exact arithmetic/model checks, not Lean kernel certificates.

## Status

- Static project/import audit: passed.
- Registry and statement-lock audits: must pass after metadata update.
- Lean/Lake kernel build: blocked because neither executable nor pinned toolchain is installed in this runtime.
- Fully independently kernel-certified numbered paper results: 0/58.
- Theorem 1.1: unproved.

## Next obligations

1. Lemma 4.3: chart-specific return estimates, Fourier regularity/Plancherel, successive-minima transference, rational projection height, and effective quadratic bound.
2. Theorem 4.7: use a verified external formalization or retain the explicit external dependency; the paper does not prove Leng–Sah–Sawhney internally.
3. Sections 5–6: derive predictor-moment replacement, adaptive approximant inheritance, delayed high-fit truncation, and full binary localization with quantitative errors.
4. Lemma 7.2: prove the randomization fourth-moment estimate, leaf-depth rectangle decomposition, clipping estimate, and short-block bound.
5. Proposition 8.9: construct the persistent PRE graph and derive chain length, Bessel rows, leakage, and offset-averaged errors.
6. Lemma 9.1: prove the separated progression-test sparse-mass estimate; current graph and density components do not imply its `delta^(1/2080)` gain by themselves.
7. Proposition 2.3: derive all local analytic budgets and restart bounds from Sections 5–9 before applying the existing finite absorption algebra.
8. Theorem 1.1: complete the Schwartz estimate and unique bounded extension; preserve the locked theorem statement.

No result is promoted to complete or kernel-verified in V51.
