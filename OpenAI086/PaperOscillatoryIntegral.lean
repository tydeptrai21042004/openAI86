import Mathlib
import OpenAI086.PaperOscillatoryPreGraph

/-! An analytic integration-by-parts bridge for Lemma 8.7. Unlike the
previous Fourier head estimate, this uses the actual interval integral
and the fundamental theorem of calculus. The derivative and reciprocal
bounds are inputs; instantiating them for every chart remains open. -/
namespace OpenAI086
open MeasureTheory intervalIntegral

/-- A primitive correction F' = e + err bounds the actual oscillatory
integral by its two boundary contributions and the integrated error. -/
theorem v23_oscillatory_ibp_bound (F e err : ℝ → ℂ) (a b A B : ℝ)
    (hder : ∀ x ∈ Set.uIcc a b, HasDerivAt F (e x+err x) x)
    (he : IntervalIntegrable e volume a b)
    (herr : IntervalIntegrable err volume a b)
    (ha : ‖F a‖ ≤ A) (hb : ‖F b‖ ≤ A)
    (hpoint : ∀ x ∈ Set.uIoc a b, ‖err x‖ ≤ B) :
    ‖∫ x in a..b, e x‖ ≤ 2*A+B*|b-a| := by
  have hft := integral_eq_sub_of_hasDerivAt hder (he.add herr)
  rw [integral_add he herr] at hft
  have hidentity : (∫ x in a..b, e x) = F b-F a-(∫ x in a..b, err x) := by
    rw [← hft]; abel
  rw [hidentity]
  calc
    _ ≤ ‖F b-F a‖+‖∫ x in a..b, err x‖ := norm_sub_le _ _
    _ ≤ (‖F b‖+‖F a‖)+B*|b-a| :=
      add_le_add (norm_sub_le _ _) (norm_integral_le_of_norm_le_const hpoint)
    _ ≤ _ := by linarith

/-- The paper has a small slope oscillation in addition to its derivative
lower bound. Under the reciprocal correction estimates this gives an
O(1/A) integral without needing a monotonicity partition. -/
theorem v23_small_slope_oscillatory_bound (F e err : ℝ → ℂ) (a b A K : ℝ)
    (hA : 0 < A) (hK : K*|b-a| ≤ A)
    (hder : ∀ x ∈ Set.uIcc a b, HasDerivAt F (e x+err x) x)
    (he : IntervalIntegrable e volume a b) (herr : IntervalIntegrable err volume a b)
    (ha : ‖F a‖ ≤ 1/A) (hb : ‖F b‖ ≤ 1/A)
    (hpoint : ∀ x ∈ Set.uIoc a b, ‖err x‖ ≤ K/A^2) :
    ‖∫ x in a..b, e x‖ ≤ 3/A := by
  have h := v23_oscillatory_ibp_bound F e err a b (1/A) (K/A^2) hder he herr ha hb hpoint
  have h' : K/A^2*|b-a| ≤ 1/A := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hA)).2
    calc
      _ ≤ A := hK
      _ = 1/A*A^2 := by field_simp [ne_of_gt hA]
  linarith

end OpenAI086
