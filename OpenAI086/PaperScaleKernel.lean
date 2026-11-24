import Mathlib

/-! The scalar continuous scale reconstruction in Lemma 2.4.
This is the actual integral on a finite positive scale window. Taking
limits, constructing the Gevrey kernel, and applying the uniform local
estimate are distinct obligations. -/
namespace OpenAI086
open MeasureTheory intervalIntegral

/-- The antiderivative of the scale kernel a⁻² ψ'(t/a), for t ≠ 0.
This direct derivative avoids a change of variables at the singular endpoint. -/
theorem v28_scale_primitive_derivative (ψ ψ' : ℝ → ℝ) (t a : ℝ)
    (ht : t ≠ 0) (ha : a ≠ 0) (hψ : HasDerivAt ψ (ψ' (t/a)) (t/a)) :
    HasDerivAt (fun s : ℝ => -(ψ (t/s))/t) (ψ' (t/a)/a^2) a := by
  have hdiv : HasDerivAt (fun s : ℝ => t/s) (-(t/a^2)) a := by
    convert (hasDerivAt_const a t).div (hasDerivAt_id a) ha using 1 <;> ring
  have hc := hψ.comp a hdiv
  have hh := hc.neg.div_const t
  convert hh using 1 <;> simp only [Function.comp_def] <;> field_simp [ht, ha] <;> ring

/-- Exact scale integral over a positive finite window. In the paper ψ is
φ''' and ψ' = φ''''. This proves the reconstruction identity prior to
endpoint limits, for both signs of t. -/
theorem v28_scale_window_identity (ψ ψ' : ℝ → ℝ) (t A B : ℝ)
    (ht : t ≠ 0) (hA : 0 < A) (hAB : A ≤ B)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hi : IntervalIntegrable (fun a => ψ' (t/a)/a^2) volume A B) :
    (∫ a in A..B, ψ' (t/a)/a^2) = (ψ (t/A)-ψ (t/B))/t := by
  have h := integral_eq_sub_of_hasDerivAt
    (f := fun a : ℝ => -(ψ (t/a))/t) (f' := fun a => ψ' (t/a)/a^2)
    (fun a ha => by
      have ha' : a ∈ Set.Icc A B := by simpa [Set.uIcc_of_le hAB] using ha
      exact v28_scale_primitive_derivative ψ ψ' t a ht (ne_of_gt (hA.trans_le ha'.1)) (hψ _)) hi
  rw [h]
  ring

end OpenAI086
