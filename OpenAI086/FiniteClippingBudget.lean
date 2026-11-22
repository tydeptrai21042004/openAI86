import Mathlib

/-!
# V6: squared finite clipping budget

The paper's Sections 5, 9 and 10 repeatedly clip a nonnegative local
contribution by a quality threshold before summing and interpolating.
This module proves the square-level elementary estimate, without
claiming the paper's stronger p in (2/3,1) power saving.
-/

namespace OpenAI086

/-- The square of a clipped nonnegative value is at most the product
of the clipping threshold and the original value. -/
theorem finite_clipped_square_le (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a) :
    (min eta a) ^ 2 ≤ eta * a := by
  have hnonneg : 0 ≤ min eta a := le_min heta ha
  calc
    (min eta a) ^ 2 = (min eta a) * (min eta a) := by ring
    _ ≤ eta * (min eta a) :=
      mul_le_mul_of_nonneg_right (min_le_left eta a) hnonneg
    _ ≤ eta * a := mul_le_mul_of_nonneg_left (min_le_right eta a) heta

/-- A summed finite clipping budget with *no factor depending on the
number of summands*. The higher-exponent interpolation and geometric
stopping argument are separate, open obligations. -/
theorem finite_clipped_square_sum_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i : ι, (min eta (a i)) ^ 2) ≤ eta * (∑ i : ι, a i) := by
  classical
  calc
    (∑ i : ι, (min eta (a i)) ^ 2) ≤ ∑ i : ι, eta * a i := by
      apply Finset.sum_le_sum
      intro i _
      exact finite_clipped_square_le eta (a i) heta (ha i)
    _ = eta * (∑ i : ι, a i) := by rw [Finset.mul_sum]

end OpenAI086
