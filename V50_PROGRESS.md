# V50 — Actual continuous L² stage projections and product increments

Source basis: October 5, 2026 manuscript, Lemma 3.4, pp. 10–13, together
with the paper's Lemma 3.3 on nested projection products.

## New module

- `OpenAI086/PaperV50StageProjectionBridge.lean`
  - Defines the local columns as actual measurable functions with explicit
    `MemLp` witnesses.
  - Builds each generation/layer subspace as the finite span of the actual
    `(spatial atom, local label)` columns in one common Bochner `L²` space.
  - Constructs actual Mathlib orthogonal projections and derives their
    integrated moment identity and constant-coefficient representations.
  - Proves one-step and arbitrary-generation subspace nesting from an
    almost-everywhere refinement identity for old columns by next-generation
    columns.
  - Applies the full Hilbert-space Lemma 3.3 to these concrete stage spans,
    obtaining both its row-prefix and square-variation conclusions under the
    row-Bessel hypothesis.
  - Shows a nonempty ordered product lies in its last-layer stage span and
    obtains its coefficient vector from span membership.
  - Proves that consecutive ordered products, represented in the newer
    inherited column family, differ exactly by the synthesis of their
    coefficient difference.

## Exact scope and remaining assumptions

The central remaining geometric input is `V50OneStepRefinement`: every
old local column must be represented almost everywhere by a finite linear
combination of the columns on the next active-anchor/terminal-cut partition.
A separate support-orthogonality proof is also needed to identify the global
span projection with the manuscript's direct sum of local projections.
The theorem does not claim to construct that representation from the paper's
mask definitions. It is the exact bridge that must be discharged by the
spatial partition and inherited-mask construction.

The new ordered-product increment theorem is an equality in the common
continuous `L²` space. Further work is required to connect its coefficient
vector to the pointwise `c(u)` fields on each anchor cell, derive the
private-coordinate pointwise lower bound on restart roots, and complete the
size-segment/attempt/representative-energy/error-row/complement/averaging
assembly of Lemma 3.4.

## Validation

- Static import/reachability, registry, statement-lock and source-safety
  audits are run by `verify_v50.sh`.
- `tools/test_v50_stage_projection.py` checks 500 exact rational finite
  models for span inclusion, nested orthogonal projections, and coefficient
  synthesis increments.
- These tests are not Lean kernel certificates and do not verify the
  geometric refinement hypothesis.

## Kernel disposition

Lean, Lake, and elan are absent in the current runtime. The V50 kernel script
fails closed with exit code 2. No result is promoted to kernel-verified.

## Next obligations

1. Derive `V50OneStepRefinement` from the exact active-anchor and terminal-cut
   partition construction, including inherited masks and terminal local refits.
2. Prove the stage labels form the paper's exact finite measurable partitions
   and that terminal atoms remain unchanged after termination.
3. Prove columns on distinct stage atoms are orthogonal, and identify the
   global span projection with the direct sum of local atom projections.
4. Identify the coefficient representation of each ordered product with the
   paper's `c(u)` on every active anchor cell.
5. Transfer the L² increment equality to the private-coordinate transition
   estimate on each restart root.
6. Derive both representative-energy caps from Lemma 3.2 and the actual
   moment representative.
7. Complete restart summation, row-error, size-segment, complement, averaging,
   and the full polylogarithmic Lemma 3.4 bound.
8. Continue Lemma 3.5 corrected vector/supremum conclusions, Lemma 4.3,
   Theorem 4.7, Sections 5–6, Section 7, Proposition 8.9, Lemma 9.1,
   Proposition 2.3, and Theorem 1.1.

No numbered paper result is promoted: 0/58 kernel-certified; Theorem 1.1
remains unproved.
