import Mathlib

/-! Actual complex Bochner integral for the corrected private-coordinate
moment in Lemma 5.3, on a normalized cell measure. This proves the
identity, not the full delayed-predictor estimate (7). -/
noncomputable section
namespace OpenAI086
open MeasureTheory

/-- Orthogonality of the augmented residual yields the corrected complex
moment, with the average of the input's private component retained.
`m` is the bilinear physical residual times the chosen predictor multiplier.
`p` is the actual input's private coordinate and `c` the private output
coefficient divided by sqrt(ε). -/
theorem v34_complex_predictor_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (m p : X → ℂ)
    (ε : ℝ) (c : ℂ) (hε : 0 ≤ ε)
    (hm : Integrable m μ) (hp : Integrable p μ)
    (hortho : (∫ x, (m x + (Real.sqrt ε : ℂ)*
      (p x - (Real.sqrt ε : ℂ)*c)) ∂μ) = 0) :
    (∫ x, m x ∂μ) = (ε : ℂ)*c - (Real.sqrt ε : ℂ)*(∫ x, p x ∂μ) := by
  have hsR : Real.sqrt ε * Real.sqrt ε = ε := by
    simpa [pow_two] using Real.sq_sqrt hε
  have hs : (Real.sqrt ε : ℂ)*(Real.sqrt ε : ℂ) = (ε : ℂ) := by
    exact_mod_cast hsR
  have hi : Integrable (fun _ : X => (Real.sqrt ε : ℂ)*c) μ := integrable_const _
  have hj : Integrable (fun x => (Real.sqrt ε : ℂ)*(p x-(Real.sqrt ε : ℂ)*c)) μ :=
    (hp.sub hi).const_mul _
  rw [integral_add hm hj, integral_const_mul, integral_sub hp hi] at hortho
  have hconst : (∫ _x : X, (Real.sqrt ε : ℂ)*c ∂μ) = (Real.sqrt ε : ℂ)*c := by
    simp [MeasureTheory.integral_const, Measure.real]
  rw [hconst] at hortho
  calc
    _ = -( (Real.sqrt ε : ℂ)*((∫ x, p x ∂μ)-(Real.sqrt ε : ℂ)*c)) := by
      linear_combination hortho
    _ = (Real.sqrt ε : ℂ)*(Real.sqrt ε : ℂ)*c -
      (Real.sqrt ε : ℂ)*(∫ x, p x ∂μ) := by ring
    _ = _ := by rw [hs]

/-- Exact difference of the two corrected moments on nested cells. The
private-coordinate averages need not coincide. -/
theorem v34_complex_predictor_increment (ε : ℝ) (a b p q : ℂ) :
    ((ε : ℂ)*b - (Real.sqrt ε : ℂ)*q) -
      ((ε : ℂ)*a - (Real.sqrt ε : ℂ)*p) =
    (ε : ℂ)*(b-a) - (Real.sqrt ε : ℂ)*(q-p) := by ring

/-- Two increments cost at most twice the sum of their energies. This is
valid in the complex case and retains the missing input increment. -/
theorem v34_predictor_increment_energy (ε : ℝ) (u v : ℂ) (hε : 0 ≤ ε) :
    ‖(Real.sqrt ε : ℂ)*(u-v)‖^2 ≤ 2*ε*(‖u‖^2+‖v‖^2) := by
  have hnorm : ‖(Real.sqrt ε : ℂ)‖ = Real.sqrt ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hnorm, mul_pow, Real.sq_sqrt hε]
  have h := norm_sub_le u v
  have hsum : 0 ≤ ‖u‖+‖v‖ := by positivity
  have hsq : ‖u-v‖^2 ≤ (‖u‖+‖v‖)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (norm_nonneg _) hsum)]
  calc
    _ ≤ ε*(‖u‖+‖v‖)^2 := mul_le_mul_of_nonneg_left hsq hε
    _ ≤ _ := by
      have hh : (‖u‖+‖v‖)^2 ≤ 2*(‖u‖^2+‖v‖^2) := by
        nlinarith [sq_nonneg (‖u‖-‖v‖)]
      nlinarith [mul_le_mul_of_nonneg_left hh hε]

end OpenAI086
