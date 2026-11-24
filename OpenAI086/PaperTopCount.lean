import Mathlib
import OpenAI086.PaperIntegratedRows

/-! Proposition 8.12: absorb the per-top error, then turn a weighted
first-top count into a measure bound. The actual first-top selection and
row estimates are separate. -/
namespace OpenAI086
open MeasureTheory

/-- The paper's error per top can be absorbed using σ² ≥ 2ε. -/
theorem v22_top_mass_absorb (σ ε mass budget : ℝ) (hσ : 0 < σ)
    (hm : 0 ≤ mass) (he : 2*ε ≤ σ^2)
    (h : σ^2*mass ≤ budget+ε*mass) : σ^2*mass ≤ 2*budget := by
  have h' := mul_le_mul_of_nonneg_right he hm
  linarith

/-- Integral Markov step for actual path counts. Integrability and
measurability of the threshold set are explicit. -/
theorem v22_top_count_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℝ) (t : ℝ) (ht : 0 < t) (hn : ∀ x, 0 ≤ N x)
    (hm : MeasurableSet {x | t ≤ N x})
    (hi : Integrable N μ)
    (hI : Integrable (({x | t ≤ N x}).indicator (fun _ : Ω => t)) μ) :
    (μ {x | t ≤ N x}).toReal ≤ (∫ x, N x ∂μ)/t := by
  have hpoint : ∀ x, ({x | t ≤ N x}).indicator (fun _ : Ω => t) x ≤ N x := by
    intro x
    by_cases hx : t ≤ N x
    · simpa [Set.indicator, hx] using hx
    · simpa [Set.indicator, hx] using hn x
  have h := integral_mono hI hi hpoint
  rw [integral_indicator hm] at h
  have he : (∫ _x in {x | t ≤ N x}, t ∂μ) = (μ {x | t ≤ N x}).toReal*t := by
    simp [MeasureTheory.integral_const, Measure.real, smul_eq_mul, mul_comm]
  rw [he] at h
  exact (le_div_iff₀ ht).2 h

/-- Distinct representatives inject into retained first tops, hence the
pathwise count is bounded by both the global label budget and top count. -/
theorem v22_top_representative_count {R T : Type*} [Fintype R] [Fintype T]
    (first : R → T) (hinj : Function.Injective first) (D A : ℕ)
    (hD : Fintype.card R ≤ D) (hA : Fintype.card T ≤ A) :
    Fintype.card R ≤ min D A :=
  le_min hD ((Fintype.card_le_of_injective first hinj).trans hA)

end OpenAI086
