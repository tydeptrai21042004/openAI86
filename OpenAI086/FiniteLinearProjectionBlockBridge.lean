import Mathlib
import OpenAI086.FiniteLinearDyadicExpansion
import OpenAI086.AugmentedNestedProjectionBlocks

/-!
# V15: exact bridge from dyadic linear-map blocks to real projection energy

`finiteLinearBlock` had a telescoping definition using `Δ₀ = P₀`.
`aligned_projection_block_energy_bound` is stated for differences of
adjacent members of a nested family. The following lemmas connect these
TWO EXACT EXPRESSIONS by prepending the zero linear operator.

This is an unconditional algebraic identity, plus a direct Bessel bound
for fixed-width dyadic blocks made from *genuine* orthogonal projections.
It closes the fixed-length Bessel premise for the one-family finite-real
case; it does NOT prove the variable-prefix row estimate by itself.
-/

namespace OpenAI086

/-- A zero linear endomorphism placed before the actual projection list. -/
def zeroPrependedLinearEnd {d : ℕ}
    (P : ℕ → FiniteRealEnd d) : ℕ → FiniteRealEnd d
  | 0 => 0
  | k + 1 => P k

/-- `Δ₀=P₀`, and `Δₙ=Pₙ-Pₙ₋₁` for `n>0`: both are precisely
adjacent differences of the zero-prepended linear endomorphism list. -/
theorem finite_linear_increment_is_augmented_difference {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k : ℕ) :
    finiteLinearIncrement P k =
      zeroPrependedLinearEnd P (k + 1) - zeroPrependedLinearEnd P k := by
  cases k with
  | zero => simp [finiteLinearIncrement, zeroPrependedLinearEnd]
  | succ k => rfl

/-- The *actual* linear block is exactly the difference between its
two augmented endpoints.  No linearity or projection property beyond
that encoded in `FiniteRealEnd` is assumed. -/
theorem finite_linear_block_augmented_endpoints {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (start width : ℕ) :
    finiteLinearBlock P start width =
      zeroPrependedLinearEnd P (start + width) -
        zeroPrependedLinearEnd P start := by
  induction width with
  | zero => simp [finiteLinearBlock]
  | succ width ih =>
      change (∑ j ∈ Finset.range (width + 1),
        finiteLinearIncrement P (start + j)) =
        zeroPrependedLinearEnd P (start + width + 1) -
          zeroPrependedLinearEnd P start
      rw [Finset.sum_range_succ]
      have hprev :
          (∑ j ∈ Finset.range width,
            finiteLinearIncrement P (start + j)) =
              zeroPrependedLinearEnd P (start + width) -
                zeroPrependedLinearEnd P start := ih
      rw [hprev, finite_linear_increment_is_augmented_difference]
      abel

/-- The function-valued and `LinearMap` zero-prepended families agree
after application to any vector. -/
theorem zero_prepended_linear_apply {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k : ℕ) (x : Fin d → ℝ) :
    (zeroPrependedLinearEnd P k) x =
      withZeroInitialProjection (fun n y => P n y) k x := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- Identifies a fixed-width linear-map dyadic block with the
corrected projection block, including the initial term `P₀`. -/
theorem finite_linear_block_is_projection_block {d : ℕ}
    (P : ℕ → FiniteRealEnd d)
    (width b : ℕ) (x : Fin d → ℝ) :
    (finiteLinearBlock P (b * width) width) x =
      paperAlignedIncrementBlock (fun n y => P n y) width b x := by
  rw [finite_linear_block_augmented_endpoints]
  simp only [LinearMap.sub_apply]
  rw [zero_prepended_linear_apply, zero_prepended_linear_apply]
  unfold paperAlignedIncrementBlock
  have hindex : b * width + width = (b + 1) * width := by ring
  simp only [hindex]

/-- **Concrete fixed-length dyadic block Bessel estimate.**
The length and number of blocks are arbitrary. No hypothetical Bessel
constant is introduced: only self-adjointness, idempotence, and nesting
of the original projections are required. -/
theorem finite_linear_dyadic_blocks_bessel {d : ℕ}
    (P : ℕ → FiniteRealEnd d)
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (width count : ℕ) (x : Fin d → ℝ) :
    (∑ b ∈ Finset.range count,
      finiteRealPair ((finiteLinearBlock P (b * width) width) x)
        ((finiteLinearBlock P (b * width) width) x)) ≤
      finiteRealPair x x := by
  have h := paper_aligned_increment_bessel
    (fun n y => P n y) hsym hidemp hnested width count x
  convert h using 1
  apply Finset.sum_congr rfl
  intro b _
  rw [finite_linear_block_is_projection_block,
      finite_linear_block_is_projection_block]

end OpenAI086
