import Mathlib
import OpenAI086.PredictorMoments

/-!
# OpenAI #086, Section 5.2: exact finite predictor energy bound

The correction to the PDF's predictor identity retains the private-input
increment. Here we also control its *square*, and the sum of those squares.
This is the algebraic energy estimate that can be fed into an eventual
conditional-expectation/L² proof. It does NOT prove the full delayed
predictor replacement estimate (7) in Lemma 5.3.
-/

namespace OpenAI086

/-- The corrected predictor increment obeys the elementary two-term
square bound, with the correct `ε` coefficient for the private input. -/
theorem predictor_increment_square_le
    (ε a₀ a₁ p₀ p₁ : ℝ) (hε : 0 ≤ ε) :
    ((ε * a₁ - Real.sqrt ε * p₁) -
      (ε * a₀ - Real.sqrt ε * p₀)) ^ 2 ≤
        2 * ε ^ 2 * (a₁ - a₀) ^ 2 +
        2 * ε * (p₁ - p₀) ^ 2 := by
  have hsq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε
  calc
    ((ε * a₁ - Real.sqrt ε * p₁) -
      (ε * a₀ - Real.sqrt ε * p₀)) ^ 2 =
        (ε * (a₁ - a₀) - Real.sqrt ε * (p₁ - p₀)) ^ 2 := by
          rw [predictor_increment_exact]
    _ ≤ 2 * (ε * (a₁ - a₀)) ^ 2 +
          2 * (Real.sqrt ε * (p₁ - p₀)) ^ 2 := by
          nlinarith [sq_nonneg (ε * (a₁ - a₀) +
            Real.sqrt ε * (p₁ - p₀))]
    _ = 2 * ε ^ 2 * (a₁ - a₀) ^ 2 +
          2 * ε * (p₁ - p₀) ^ 2 := by
          simp only [mul_pow, hsq]
          ring

/-- A finite square-energy bound: the missing private-input term persists
when predictor moments are summed over many disjoint rows. -/
theorem predictor_increment_finite_energy
    {ι : Type*} (s : Finset ι)
    (ε : ℝ) (hε : 0 ≤ ε)
    (a₀ a₁ p₀ p₁ : ι → ℝ) :
    (∑ i ∈ s,
      ((ε * a₁ i - Real.sqrt ε * p₁ i) -
        (ε * a₀ i - Real.sqrt ε * p₀ i)) ^ 2) ≤
      2 * ε ^ 2 * (∑ i ∈ s, (a₁ i - a₀ i) ^ 2) +
      2 * ε * (∑ i ∈ s, (p₁ i - p₀ i) ^ 2) := by
  calc
    (∑ i ∈ s,
      ((ε * a₁ i - Real.sqrt ε * p₁ i) -
        (ε * a₀ i - Real.sqrt ε * p₀ i)) ^ 2) ≤
        ∑ i ∈ s,
          (2 * ε ^ 2 * (a₁ i - a₀ i) ^ 2 +
            2 * ε * (p₁ i - p₀ i) ^ 2) := by
              apply Finset.sum_le_sum
              intro i _
              exact predictor_increment_square_le ε (a₀ i) (a₁ i) (p₀ i) (p₁ i) hε
    _ = 2 * ε ^ 2 * (∑ i ∈ s, (a₁ i - a₀ i) ^ 2) +
          2 * ε * (∑ i ∈ s, (p₁ i - p₀ i) ^ 2) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

end OpenAI086
