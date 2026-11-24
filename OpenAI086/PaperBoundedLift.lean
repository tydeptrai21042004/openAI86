import Mathlib
import OpenAI086.PaperSeparatedRows

/-! Lemma 8.1: pointwise physical correction and private-coordinate lift
energy. The first-match Fourier expansion and choice of weights must
still be derived from the actual chart data. -/
namespace OpenAI086

/-- Correction on the physical coordinate: only the active primary
count enters the Cauchy–Schwarz bound. -/
theorem v22_lift_physical_correction {I : Type*} [Fintype I]
    (a q : I → ℂ) (δ E : ℝ) (hδ : 0 ≤ δ)
    (hq : ∀ i, ‖q i‖ ≤ δ) (ha : (∑ i, ‖a i‖^2) ≤ E) :
    ‖∑ i, a i*q i‖^2 ≤ (Fintype.card I : ℝ)*δ^2*E := by
  classical
  have htri : ‖∑ i, a i*q i‖ ≤ δ*(∑ i, ‖a i‖) := by
    calc
      _ ≤ ∑ i, ‖a i*q i‖ := norm_sum_le _ _
      _ ≤ ∑ i, δ*‖a i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, mul_comm δ]
        exact mul_le_mul_of_nonneg_left (hq i) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hCS := v20_path_synthesis_square (Finset.univ : Finset I) (fun i => ‖a i‖)
    (Fintype.card I : ℝ) (by simp)
  have hsq := pow_le_pow_left₀ (norm_nonneg (∑ i, a i*q i)) htri 2
  calc
    _ ≤ (δ*(∑ i, ‖a i‖))^2 := hsq
    _ ≤ δ^2*((Fintype.card I : ℝ)*(∑ i, ‖a i‖^2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by simpa using hCS) (sq_nonneg δ)
    _ ≤ _ := by
      rw [← mul_assoc, mul_comm (δ^2)]
      exact mul_le_mul_of_nonneg_left ha (by positivity)

/-- Each primary's mode weight sum is at most one. Consequently the
mode-coordinate map is a contraction, without a factor for mode count. -/
theorem v22_lift_private_energy {I M : Type*} [Fintype I] [Fintype M]
    (a : I → ℝ) (w : I → M → ℝ)
    (hw : ∀ i, (∑ m, (w i m)^2) ≤ 1) :
    (∑ i, ∑ m, (a i*w i m)^2) ≤ ∑ i, (a i)^2 := by
  apply Finset.sum_le_sum
  intro i _
  simp only [mul_pow, ← Finset.mul_sum]
  simpa using mul_le_mul_of_nonneg_left (hw i) (sq_nonneg (a i))

end OpenAI086
