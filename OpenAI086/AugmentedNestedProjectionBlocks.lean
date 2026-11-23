import Mathlib
import OpenAI086.FiniteAlignedProjectionBlocks

/-!
# V15: incorporating the initial projection in dyadic Bessel blocks

The manuscript's increments are `Δ₀ = P₀` and `Δₙ = Pₙ - Pₙ₋₁`
for `n > 0`. An ordinary sequence of differences beginning at `P₀`
misses `Δ₀`.  Introduce the ZERO projection immediately before `P₀`:

  `P̂ 0 = 0`,  `P̂ (n+1) = P n`.

The already proved aligned-block Bessel inequality then applies to
*all* increments, including the crucial initial one, with sharp
constant one.  This is an actual nested-projection hypothesis, not an
assumed block-energy estimate.  It concerns ONE projection family;
the row-adaptive m-layer prefix estimate remains a separate goal.
-/

namespace OpenAI086

/-- Insert a zero projection before the first genuine projection. -/
def withZeroInitialProjection {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ)) :
    ℕ → (Fin d → ℝ) → (Fin d → ℝ)
  | 0 => fun _ => 0
  | n + 1 => P n

/-- The augmented family remains self-adjoint. -/
theorem with_zero_initial_self_adjoint {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v)) :
    ∀ k u v,
      finiteRealPair (withZeroInitialProjection P k u) v =
        finiteRealPair u (withZeroInitialProjection P k v) := by
  intro k u v
  cases k with
  | zero => simp [withZeroInitialProjection, finiteRealPair]
  | succ k => exact hsym k u v

/-- Zero is itself an idempotent orthogonal projection. -/
theorem with_zero_initial_idempotent {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hidemp : ∀ k u, P k (P k u) = P k u) :
    ∀ k u,
      withZeroInitialProjection P k
        (withZeroInitialProjection P k u) =
        withZeroInitialProjection P k u := by
  intro k u
  cases k with
  | zero => simp [withZeroInitialProjection]
  | succ k => exact hidemp k u

/-- Nestedness is preserved by the initial zero member. -/
theorem with_zero_initial_nested {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u) :
    ∀ k u,
      withZeroInitialProjection P k
        (withZeroInitialProjection P (k + 1) u) =
        withZeroInitialProjection P k u := by
  intro k u
  cases k with
  | zero => simp [withZeroInitialProjection]
  | succ k => exact hnested k u

/-- An aligned dyadic block of the actual paper increments:
`sum_{j=bw}^{(b+1)w-1} Δⱼ = P̂ ((b+1)w) - P̂ (bw)`.
The definition also works for arbitrary positive integer widths. -/
def paperAlignedIncrementBlock {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (width block : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  withZeroInitialProjection P ((block + 1) * width) x -
    withZeroInitialProjection P (block * width) x

/-- Actual aligned prefix blocks of the family have total Bessel
energy at most that of the input, uniformly in the number of blocks.
The block at position zero includes `P₀`, not merely `P₁-P₀`. -/
theorem paper_aligned_increment_bessel {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (width count : ℕ) (x : Fin d → ℝ) :
    (∑ b ∈ Finset.range count,
      finiteRealPair (paperAlignedIncrementBlock P width b x)
        (paperAlignedIncrementBlock P width b x)) ≤
      finiteRealPair x x := by
  have h := aligned_projection_block_energy_bound
    (withZeroInitialProjection P)
    (with_zero_initial_self_adjoint P hsym)
    (with_zero_initial_idempotent P hidemp)
    (with_zero_initial_nested P hnested)
    0 width count x
  simpa only [paperAlignedIncrementBlock,
    alignedProjectionBlock, Nat.zero_add] using h

/-- In particular, the initial one-step block is exactly `P₀ x`. -/
theorem paper_first_block_exact {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (x : Fin d → ℝ) :
    paperAlignedIncrementBlock P 1 0 x = P 0 x := by
  simp [paperAlignedIncrementBlock, withZeroInitialProjection]

end OpenAI086
