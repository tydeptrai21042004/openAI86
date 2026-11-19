import Mathlib

/-!
# OpenAI #086, Lemma 3.4: exact finite path-label energy budget

The paper needs the pointwise integral bound
  sum_v ||1_R Phi_v||² <= D³ |R|.
We establish its independent pointwise finite-label inequality.  The
integral and the remaining cell-dependent operator compression are open.
-/

namespace OpenAI086

/-- A finite family with at most `D` active labels, each of norm at most
`D`, has total squared energy at most `D³`. -/
theorem finite_path_label_energy
    {α E : Type*} [DecidableEq α] [NormedAddCommGroup E]
    (active : Finset α) (Φ : α → E) (D : ℝ)
    (hD : 0 ≤ D)
    (hcard : (active.card : ℝ) ≤ D)
    (hbound : ∀ v ∈ active, ‖Φ v‖ ≤ D) :
    (∑ v ∈ active, ‖Φ v‖ ^ 2) ≤ D ^ 3 := by
  calc
    (∑ v ∈ active, ‖Φ v‖ ^ 2) ≤ ∑ _v ∈ active, D ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      have hnorm : 0 ≤ ‖Φ v‖ := norm_nonneg _
      have hl := hbound v hv
      nlinarith [mul_nonneg (sub_nonneg.mpr hl) (add_nonneg hnorm hD)]
    _ = (active.card : ℝ) * D ^ 2 := by simp
    _ ≤ D ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcard) (sq_nonneg D)]

/-- Common squared error amplitudes factor out of the path-label budget. -/
theorem finite_path_label_error_energy
    {α E : Type*} [DecidableEq α] [NormedAddCommGroup E]
    (active : Finset α) (Φ : α → E) (D error : ℝ)
    (hD : 0 ≤ D)
    (hcard : (active.card : ℝ) ≤ D)
    (hbound : ∀ v ∈ active, ‖Φ v‖ ≤ D) :
    (∑ v ∈ active, error ^ 2 * ‖Φ v‖ ^ 2) ≤
      error ^ 2 * D ^ 3 := by
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (finite_path_label_energy active Φ D hD hcard hbound)
    (sq_nonneg error)

end OpenAI086
