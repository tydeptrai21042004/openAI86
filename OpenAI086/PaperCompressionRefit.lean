import Mathlib
import OpenAI086.PaperCompressionVectorRows

/-! Quantitative refit estimate in Lemma 3.2 and Lemma 3.4.
The normalized integral and coefficient coercivity suffice; an explicit
inverse Gram matrix is not needed for this bound. Existence of the local
orthogonal projection and its moment identities still need a bridge. -/
namespace OpenAI086
open MeasureTheory

/-- Scalar core of the normalized refit bound. -/
theorem v38_refit_coefficient (c D U F E : ℝ)
    (hc : 0 ≤ c) (hD : 0 < D)
    (hlower : c^2 / D^2 ≤ E) (hupper : E ≤ U*c*F) :
    c ≤ D^2*U*F ∨ c = 0 := by
  by_cases h : c = 0
  · exact Or.inr h
  · left
    have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm h)
    have hd2 : 0 < D^2 := sq_pos_of_pos hD
    have h1 := (div_le_iff₀ hd2).mp (hlower.trans hupper)
    apply (mul_le_mul_left hcpos).mp
    calc
      c*c = c^2 := by ring
      _ ≤ U*c*F*D^2 := h1
      _ = c*(D^2*U*F) := by ring

/-- The refitted function obeys the paper's D^5 normalized L¹-to-L∞
bound once its coefficient coercivity, upper synthesis bound and
orthogonality energy inequality are supplied. This theorem integrates
actual real functions on a probability space, not point samples. -/
theorem v38_refit_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (D c : ℝ) (hD : 0 < D) (hc : 0 ≤ c)
    (hf : ∀ x, 0 ≤ f x)
    (hlower : ∀ x, c^2/D^2 ≤ (g x)^2)
    (hupper : ∀ x, g x ≤ D*Real.sqrt D*c)
    (hfi : Integrable f μ) (hgi : Integrable (fun x => (g x)^2) μ)
    (hfg : Integrable (fun x => f x*g x) μ)
    (hmoment : (∫ x, (g x)^2 ∂μ) ≤ ∫ x, f x*g x ∂μ) :
    ∀ x, g x ≤ D^5*(∫ y, f y ∂μ) := by
  let U := D*Real.sqrt D
  let F := ∫ x, f x ∂μ
  let E := ∫ x, (g x)^2 ∂μ
  have hU : 0 ≤ U := mul_nonneg hD.le (Real.sqrt_nonneg _)
  have hF : 0 ≤ F := integral_nonneg hf
  have hlo : c^2/D^2 ≤ E := by
    have h := integral_mono (integrable_const (c^2/D^2)) hgi hlower
    simpa [E] using h
  have hup : E ≤ U*c*F := by
    apply hmoment.trans
    have h := integral_mono hfg (hfi.const_mul (U*c)) (fun x => by
      calc
        f x*g x ≤ f x*(U*c) := mul_le_mul_of_nonneg_left (hupper x) (hf x)
        _ = U*c*f x := by ring)
    simpa [F, integral_const_mul] using h
  have hcoef : c ≤ D^2*U*F := by
    rcases v38_refit_coefficient c D U F E hc hD hlo hup with h | h
    · exact h
    · rw [h]
      exact mul_nonneg (mul_nonneg (sq_nonneg D) hU) hF
  have hU2 : U^2 = D^3 := by
    dsimp [U]
    rw [mul_pow, Real.sq_sqrt hD.le]
    ring
  intro x
  calc
    g x ≤ U*c := hupper x
    _ ≤ U*(D^2*U*F) := mul_le_mul_of_nonneg_left hcoef hU
    _ = D^2*U^2*F := by ring
    _ = D^5*F := by rw [hU2]; ring

end OpenAI086
