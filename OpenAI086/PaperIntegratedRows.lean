import Mathlib
import OpenAI086.PaperSeparatedRows

/-! Lemma 8.7: integrate the actual pathwise overlap bound. This is valid
for any measure space, not only a finite spatial model. Integrability of
the displayed square sums is explicit. -/
namespace OpenAI086
open MeasureTheory

/-- Pointwise multiplicity, followed by integration. The set of rows
active at a point may vary arbitrarily; only the pointwise cardinal counts. -/
theorem v21_integrated_path_synthesis {Ω I : Type*} [MeasurableSpace Ω]
    [DecidableEq I] (μ : Measure Ω) (active : Ω → Finset I)
    (b : I → Ω → ℝ) (D : ℝ)
    (hD : ∀ x, ((active x).card : ℝ) ≤ D)
    (hL : Integrable (fun x => (∑ i ∈ active x, b i x)^2) μ)
    (hR : Integrable (fun x => ∑ i ∈ active x, (b i x)^2) μ) :
    (∫ x, (∑ i ∈ active x, b i x)^2 ∂μ) ≤
      D*(∫ x, ∑ i ∈ active x, (b i x)^2 ∂μ) := by
  have h := integral_mono hL (hR.const_mul D)
    (fun x => v20_path_synthesis_square (active x) (fun i => b i x) D (hD x))
  simpa only [integral_const_mul] using h

/-- For a finite collection of measurable supports and constant row
coefficients, integrate the sum of the supported squared coefficients.
The support integrability hypothesis is explicit. -/
theorem v21_integral_supported_square_sum {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) (J : I → Set Ω) (b : I → ℝ)
    (hm : ∀ i, MeasurableSet (J i)) (hf : ∀ i, μ (J i) ≠ ⊤)
    (hi : ∀ i, Integrable ((J i).indicator (fun _ : Ω => (b i)^2)) μ) :
    (∫ x, ∑ i, (J i).indicator (fun _ : Ω => (b i)^2) x ∂μ) =
      ∑ i, (μ (J i)).toReal*(b i)^2 := by
  classical
  rw [integral_finset_sum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hm i)]
  simp [MeasureTheory.integral_const, Measure.real, smul_eq_mul, mul_comm]

/-- Integrated cross-term closure, using explicit pointwise and integrated
bounds from the row synthesis. The exponent cost is D³ times the overlap
coefficient. -/
theorem v21_integrated_separated_budget {Ω I : Type*} [MeasurableSpace Ω]
    [DecidableEq I] (μ : Measure Ω) (active : Ω → Finset I)
    (b : I → Ω → ℝ) (D ε S B cross : ℝ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hcard : ∀ x, ((active x).card : ℝ) ≤ D)
    (hL : Integrable (fun x => (∑ i ∈ active x, b i x)^2) μ)
    (hR : Integrable (fun x => ∑ i ∈ active x, (b i x)^2) μ)
    (hcross : cross ≤ ε*(∫ x, (∑ i ∈ active x, b i x)^2 ∂μ))
    (hpriv : (∫ x, ∑ i ∈ active x, (b i x)^2 ∂μ) ≤ D^2*B)
    (hdiag : S ≤ B+cross) : S ≤ (1+ε*D^3)*B := by
  have h1 := v21_integrated_path_synthesis μ active b D hcard hL hR
  have h2 := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hpriv hD)) hε
  apply v20_separated_synthesis_budget S cross B D ε hD hε hdiag
  calc
    cross ≤ ε*(∫ x, (∑ i ∈ active x, b i x)^2 ∂μ) := hcross
    _ ≤ ε*(D*(D^2*B)) := h2
    _ = ε*D*D^2*B := by ring

end OpenAI086
