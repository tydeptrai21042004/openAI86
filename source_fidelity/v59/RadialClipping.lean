import Mathlib

/-! Paper Lemma 7.2, p.56: radial clipping of the possible heavy slot.
This module proves the original pointwise and integrated L¹ deletion
estimate directly, without assuming a clipping error inequality. -/
namespace OpenAI086.PaperV59
open MeasureTheory

noncomputable def radialClip (A : ℝ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ A then z else (A / ‖z‖) • z

theorem measurable_radialClip (A : ℝ) : Measurable (radialClip A) := by
  unfold radialClip
  exact Measurable.ite (measurableSet_le measurable_id.norm measurable_const) measurable_id
    ((measurable_const.div measurable_id.norm).smul measurable_id)

theorem norm_radialClip_le (A : ℝ) (hA : 0 < A) (z : ℂ) : ‖radialClip A z‖ ≤ A := by
  by_cases h : ‖z‖ ≤ A
  · simpa [radialClip, h] using h
  · have hz : 0 < ‖z‖ := lt_trans hA (lt_of_not_ge h)
    rw [radialClip, if_neg h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hA.le hz.le), div_mul_cancel₀ _ hz.ne']

theorem norm_radialClip_le_self (A : ℝ) (hA : 0 < A) (z : ℂ) :
    ‖radialClip A z‖ ≤ ‖z‖ := by
  by_cases h : ‖z‖ ≤ A
  · simp [radialClip, h]
  · exact (norm_radialClip_le A hA z).trans (lt_of_not_ge h).le

/-- The exact pointwise loss, including at z=0. -/
theorem norm_radialClip_error (A : ℝ) (hA : 0 < A) (z : ℂ) :
    ‖z - radialClip A z‖ = max 0 (‖z‖ - A) := by
  by_cases h : ‖z‖ ≤ A
  · simp [radialClip, h, max_eq_left (sub_nonpos.mpr h)]
  · have hz : 0 < ‖z‖ := lt_trans hA (lt_of_not_ge h)
    have hc : 0 ≤ 1 - A / ‖z‖ := sub_nonneg.mpr
      ((div_le_one hz).mpr (lt_of_not_ge h).le)
    rw [radialClip, if_neg h, max_eq_right (sub_nonneg.mpr (lt_of_not_ge h).le)]
    calc
      ‖z - (A / ‖z‖) • z‖ = ‖(1 - A / ‖z‖) • z‖ := by rw [sub_smul, one_smul]
      _ = (1 - A / ‖z‖) * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      _ = ‖z‖ - A := by field_simp <;> ring

theorem radialClip_error_le (A : ℝ) (hA : 0 < A) (z : ℂ) :
    ‖z - radialClip A z‖ ≤ A⁻¹ * ‖z‖^2 := by
  rw [norm_radialClip_error A hA]
  by_cases h : ‖z‖ ≤ A
  · rw [max_eq_left (sub_nonpos.mpr h)]
    positivity
  · rw [max_eq_right (sub_nonneg.mpr (lt_of_not_ge h).le), ← div_eq_inv_mul]
    apply (le_div_iff₀ hA).mpr
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr (lt_of_not_ge h).le)]

/-- On any measure space with square-integrable norm, the actual clipping
error is integrable and has the L¹ estimate used by the paper. -/
theorem integral_radialClip_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : ℝ) (hA : 0 < A) (f : X → ℂ) (hf : Measurable f)
    (h2 : Integrable (fun x => ‖f x‖^2) μ) :
    Integrable (fun x => ‖f x - radialClip A (f x)‖) μ ∧
    (∫ x, ‖f x - radialClip A (f x)‖ ∂μ) ≤ A⁻¹ * ∫ x, ‖f x‖^2 ∂μ := by
  have hd := h2.const_mul A⁻¹
  have hm : Measurable (fun x => ‖f x - radialClip A (f x)‖) :=
    (hf.sub ((measurable_radialClip A).comp hf)).norm
  have hi : Integrable (fun x => ‖f x - radialClip A (f x)‖) μ := by
    refine hd.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact radialClip_error_le A hA (f x)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, A⁻¹ * ‖f x‖^2 ∂μ := integral_mono hi hd (fun x => radialClip_error_le A hA (f x))
    _ = _ := integral_const_mul _ _
end OpenAI086.PaperV59
#print axioms OpenAI086.PaperV59.norm_radialClip_error
#print axioms OpenAI086.PaperV59.radialClip_error_le
#print axioms OpenAI086.PaperV59.integral_radialClip_error
