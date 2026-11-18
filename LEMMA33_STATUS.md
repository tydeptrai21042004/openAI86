> **Whole-project packaging update:** The new `OpenAI086Whole.lean` entrypoint imports the Lemma 3.3 candidate and core together. Theorem 1.1 remains unproved, and kernel compilation has not been confirmed in this environment.

# Lemma 3.3: audited integration status

## PDF statement (OpenAI #086, page 9)

Let `Pᵢₙ` be a nested family of orthogonal projections in each layer
`i=1,…,m` (no commutativity across layers). Let
`Zₙ=Pᵐₙ⋯P¹ₙ` and `L_T = 1 + ⌈log₂(T+1)⌉`.

For rows satisfying `Σ_ν ‖B_νh‖² ≤ ‖h‖²`, the first bound is

`Σ_ν ‖B_ν Z_{n(ν)} g‖² ≤ L_T^(2m) ‖g‖²`.

The second bound is

`Σ_{n=1}^T ‖(Z_n-Z_{n-1})g‖² ≤ m² L_T^(2(m-1)) ‖g‖²`.

The standalone Lean module `Lemma33Reviewed.lean` contains proof scripts
for both estimates, including fully noncommuting products; it **does not**
assume layer commutation. It handles a common codomain `F` for all row maps.
The paper permits row-dependent codomains `Y_ν`; that additional level of
generality is **not** yet formalized here. This is a significant scope note,
not merely a cosmetic detail.

## Mathematical dependency audit

1. **Dyadic prefix bound**: binary split at a power of two; disjoint rows
   are added in ℓ², complete blocks by Bessel, yielding a factor `1+k`.
2. **Single nested family**: increments `P_0`, `P_n-P_(n-1)` are mutually
   orthogonal and have total energy at most the original input energy.
3. **Many layers**: recursively absorb the outermost projection into the
   row maps; rescale by `L_T^(-1)` to restore the row contraction. No
   commutation of different layers occurs.
4. **Jumps**: telescope `Z_n-Z_(n-1)` one layer at a time and apply
   row-prefix to the preceding layers; difference rows are Bessel.

## What has and has not been verified

- Source excerpt and dependencies were reviewed against PDF page 9.
- No imported reference theorem: only Mathlib is imported.
- The code is derived from the reviewed reference, so **proof authorship is not independent**.
- Static checks can verify shape, theorem existence and absence of placeholders.
- Lean kernel compilation was unavailable in this container, so the module
  is a **candidate**, not an independently executed proof certificate.
- Lemma 3.4 (compression) remains incomplete in the user-owned project.
- Theorem 1.1 is not proved by this incremental package.

## Build

```bash
bash verify.sh
lake env lean OpenAI086/Lemma33Reviewed.lean
lake env lean OpenAI086.lean
```

Check `#print axioms` output; only accepted Lean/Mathlib foundational axioms
should remain, not project-introduced assumptions.


**Integration decision:** kept as a separate candidate; no merge into
`OpenAI086.lean` because local kernel verification was not available.
