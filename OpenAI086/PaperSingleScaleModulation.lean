import Mathlib

/-! Lemma 4.6 (pp.21–22): exact separation of the linear modulation,
and multiplier estimate in a Hilbert Fourier model. The continuous
Plancherel realization and chart tail estimates remain open. -/
namespace OpenAI086

theorem v26_progression_modulation_phase (a b γ ya yb : ℝ) (hab : a ≠ b) :
    γ*((yb-ya)/(b-a)) = (-γ/(b-a))*ya+(γ/(b-a))*yb := by
  have h : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp
  <;> ring

theorem v26_progression_modulation (a b γ ya yb : ℝ) (hab : a ≠ b) :
    Complex.exp (Complex.I * (↑(γ*((yb-ya)/(b-a))) : ℂ)) =
      Complex.exp (Complex.I * (↑((-γ/(b-a))*ya) : ℂ)) *
      Complex.exp (Complex.I * (↑((γ/(b-a))*yb) : ℂ)) := by
  rw [v26_progression_modulation_phase a b γ ya yb hab]
  push_cast
  rw [mul_add, Complex.exp_add]

/-- The Fourier multiplier estimate is independent of the index count.
The actual continuous Fourier transform must still supply Plancherel. -/
theorem v26_multiplier_energy {I : Type*} (s : Finset I)
    (m f : I → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hm : ∀ i ∈ s, ‖m i‖ ≤ A) :
    ∑ i ∈ s, ‖m i*f i‖^2 ≤ A^2*(∑ i ∈ s, ‖f i‖^2) := by
  calc
    _ ≤ ∑ i ∈ s, A^2*‖f i‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hm i hi) 2) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end OpenAI086
