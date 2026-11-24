import Mathlib

/-! Lemma 5.7, p.37: cancellation at a tiny t-frequency after removing
the effective quadratic phase. The integration is over an actual real
interval, with the exact zero marginal as input. -/
namespace OpenAI086
open MeasureTheory intervalIntegral

theorem v27_tiny_frequency_marginal (w f : ℝ → ℂ) (a b M ε : ℝ)
    (c : ℂ) (hw : IntervalIntegrable w volume a b)
    (hf : IntervalIntegrable (fun t => w t*f t) volume a b)
    (hzero : (∫ t in a..b, w t) = 0)
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hbound : ∀ t ∈ Set.uIoc a b, ‖w t‖ ≤ M)
    (hsmall : ∀ t ∈ Set.uIoc a b, ‖f t-c‖ ≤ ε) :
    ‖∫ t in a..b, w t*f t‖ ≤ M*ε*|b-a| := by
  have hc : IntervalIntegrable (fun t => w t*c) volume a b := hw.mul_const c
  have hid : (∫ t in a..b, w t*f t) = ∫ t in a..b, w t*(f t-c) := by
    have hfun : (fun t => w t*(f t-c)) = (fun t => w t*f t-w t*c) := by
      funext t; ring
    rw [hfun, integral_sub hf hc, integral_mul_const, hzero, zero_mul, sub_zero]
  rw [hid]
  apply norm_integral_le_of_norm_le_const
  intro t ht
  rw [norm_mul]
  exact mul_le_mul (hbound t ht) (hsmall t ht) (norm_nonneg _) hM

/-- In the pure constant-frequency case the actual marginal is exactly zero. -/
theorem v27_constant_marginal (w : ℝ → ℂ) (a b : ℝ) (c : ℂ)
    (hzero : (∫ t in a..b, w t) = 0) :
    (∫ t in a..b, w t*c) = 0 := by
  rw [integral_mul_const, hzero, zero_mul]

end OpenAI086
