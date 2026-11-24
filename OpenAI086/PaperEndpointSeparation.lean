import Mathlib
import OpenAI086.PaperIntegratedRows

/-! Lemma 6.5: combine repeated occurrences BEFORE bounding coefficients.
The pointwise path bound and integrated cross-term closure are independent
of the number of endpoint times. The oscillatory grid bound is still an
input; no claim of the full lemma is made. -/
namespace OpenAI086
open MeasureTheory

/-- Combine all occurrences of one label on an actual measurable space.
Repeated occurrences and their cancellations are retained. -/
noncomputable def v22EndpointCoeff {I Ω : Type*} [Fintype I]
    (cell : I → Set Ω) (a : I → ℂ) (x : Ω) : ℂ := by
  classical
  exact ∑ i, (cell i).indicator (fun _ => a i) x

/-- A product of combined coefficients expands into cell intersections,
not a count of all occurrences. Useful for the common last-separation grid. -/
theorem v22_endpoint_product {I J Ω : Type*} [Fintype I] [Fintype J]
    (C : I → Set Ω) (D : J → Set Ω) (a : I → ℂ) (b : J → ℂ) (x : Ω) :
    v22EndpointCoeff C a x * v22EndpointCoeff D b x =
      ∑ i, ∑ j, (C i ∩ D j).indicator (fun _ => a i*b j) x := by
  classical
  unfold v22EndpointCoeff
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : x ∈ C i <;> by_cases hj : x ∈ D j <;>
    simp [Set.indicator, hi, hj]

/-- A private direction recovers the combined coefficient, with the
inverse weight W. The estimate does not require the coefficient to be
constant on the entire root. -/
theorem v22_private_combined_coeff {I : Type*} [Fintype I]
    (a : I → ℂ) (w : I → ℝ) (W E : ℝ) (hW : 0 ≤ W)
    (hw : ∀ i, 0 ≤ w i ∧ 1 ≤ W*w i)
    (hE : (∑ i, (w i*‖a i‖)^2) ≤ E) :
    (∑ i, ‖a i‖^2) ≤ W^2*E := by
  calc
    _ ≤ ∑ i, (W*(w i*‖a i‖))^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_right (hw i).2 (norm_nonneg (a i))
      rw [one_mul, mul_assoc] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = W^2*(∑ i, (w i*‖a i‖)^2) := by simp [mul_pow, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg W)

/-- The integrated endpoint synthesis bound after the common-grid
oscillatory pair estimate. Here D counts active (group,label) pairs,
W is the inverse private-coordinate weight, and ε is the pair bound. -/
theorem v22_endpoint_synthesis {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) (active : Ω → Finset I) (a : I → Ω → ℝ)
    (D W ε E cross S : ℝ) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hc : ∀ x, ((active x).card : ℝ) ≤ D)
    (hL : Integrable (fun x => (∑ i ∈ active x, a i x)^2) μ)
    (hR : Integrable (fun x => ∑ i ∈ active x, (a i x)^2) μ)
    (hcross : cross ≤ ε*(∫ x, (∑ i ∈ active x, a i x)^2 ∂μ))
    (hpriv : (∫ x, ∑ i ∈ active x, (a i x)^2 ∂μ) ≤ W^2*E)
    (hdiag : S ≤ E+cross) : S ≤ (1+ε*D*W^2)*E := by
  have h := v21_integrated_path_synthesis μ active a D hc hL hR
  have h' := h.trans (mul_le_mul_of_nonneg_left hpriv hD)
  calc
    S ≤ E+cross := hdiag
    _ ≤ E+ε*(D*(W^2*E)) := add_le_add_left
      (hcross.trans (mul_le_mul_of_nonneg_left h' hε)) E
    _ = _ := by ring

end OpenAI086
