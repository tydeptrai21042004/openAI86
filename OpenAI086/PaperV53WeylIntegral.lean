import OpenAI086.PaperV52IteratedWeylSamples

/-! Lemma 4.3, p.17: integrate the pointwise modulation/translation
identity and its error. No claim of the chart-specific identity, Haar
change of variables, or Fourier-ball estimates is made here. -/
namespace OpenAI086
open MeasureTheory

/-- Exact integral perturbation with the full L1 error, not a presumed
bound on the difference of Fourier samples. -/
theorem v53_integral_modulation_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F G E : X → ℂ) (u : ℂ) (e : ℝ)
    (hG : Integrable G μ) (hE : Integrable E μ)
    (hid : ∀ x, F x = u*G x+E x)
    (he : (∫ x, ‖E x‖ ∂μ) ≤ e) :
    ‖(∫ x, F x ∂μ)-u*(∫ x, G x ∂μ)‖ ≤ e := by
  have hfun : F = fun x => u*G x+E x := funext hid
  rw [hfun, integral_add (hG.const_mul u) hE, integral_const_mul, add_sub_cancel_left]
  exact (norm_integral_le_integral_norm E).trans he

/-- Feed an actual pointwise identity into the V52 recurrence, allowing
an independent unit phase and an integrable error at each step. -/
theorem v53_integrated_sample_propagation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℂ) (E : ℕ → X → ℂ)
    (u : ℕ → ℂ) (M : ℕ) (δ e : ℝ)
    (hδ : 0 < δ) (he : 0 ≤ e)
    (hF : ∀ j ≤ M, Integrable (F j) μ)
    (hE : ∀ j < M, Integrable (E j) μ)
    (hu : ∀ j < M, ‖u j‖ = 1)
    (hid : ∀ j < M, ∀ x, F (j+1) x = u j*F j x+E j x)
    (herror : ∀ j < M, (∫ x, ‖E j x‖ ∂μ) ≤ e)
    (hinit : 3*δ/4 ≤ ‖∫ x, F 0 x ∂μ‖)
    (hbudget : (M:ℝ)*e ≤ δ/4) :
    ∀ j ≤ M, δ/2 ≤ ‖∫ x, F j x ∂μ‖ := by
  apply v52_iterated_sample_lower_bound (fun j => ∫ x, F j x ∂μ) M δ e hδ he hinit ?_ hbudget
  intro j hj
  exact ⟨u j, hu j hj, v53_integral_modulation_error μ (F (j+1)) (F j) (E j)
    (u j) e (hF j hj.le) (hE j hj) (hid j hj) (herror j hj)⟩

end OpenAI086
