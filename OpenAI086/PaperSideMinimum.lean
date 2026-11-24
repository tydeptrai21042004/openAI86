import Mathlib

/-! Proposition 7.5 and Section 10: the original cell minimum is taken
before estimating powered terms. Absolute errors are charged without a
power. The analytic side, core, and near-band estimates are not assumed
proved by this algebraic assembly. -/
namespace OpenAI086

/-- Split an absolute error off from the minimum, without any power loss. -/
theorem v24_min_add_error (η a b : ℝ) (hb : 0 ≤ b) :
    min η (a+b) ≤ min η a+b := by
  by_cases h : a ≤ η
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left _ _).trans (by linarith)

/-- The exact gain used in Sections 7, 9 and 10. -/
theorem v24_min_power (η a p : ℝ) (hη : 0 < η) (ha : 0 ≤ a)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    min η a ≤ η ^ (1-p) * a ^ p := by
  by_cases h : a ≤ η
  · rw [min_eq_right h]
    by_cases h0 : a = 0
    · subst a; simp [Real.zero_rpow (ne_of_gt hp)]
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
      calc
        a = a ^ (1-p) * a ^ p := by rw [← Real.rpow_add ha']; simp
        _ ≤ η ^ (1-p) * a ^ p :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha h (by linarith)) (Real.rpow_nonneg ha _)
  · rw [min_eq_left (le_of_not_ge h)]
    calc
      η = η ^ (1-p) * η ^ p := by rw [← Real.rpow_add hη]; simp
      _ ≤ η ^ (1-p) * a ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hη.le (le_of_not_ge h) hp.le)
          (Real.rpow_nonneg hη.le _)

/-- Do not take a fractional power of an absolute error or near-band term. -/
theorem v24_min_power_with_error (η a b p : ℝ) (hη : 0 < η)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 < p) (hp1 : p ≤ 1) :
    min η (a+b) ≤ η ^ (1-p) * a ^ p+b :=
  (v24_min_add_error η a b hb).trans (add_le_add_right (v24_min_power η a p hη ha hp hp1) b)

/-- Weighted cell sum, with all group and coupled-band contributions already
combined at each cell. -/
theorem v24_weighted_min_assembly {I : Type*} (s : Finset I)
    (w a b : I → ℝ) (η p : ℝ) (hη : 0 < η) (hp : 0 < p) (hp1 : p ≤ 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ i ∈ s, w i * min η (a i+b i)) ≤
      η ^ (1-p) * (∑ i ∈ s, w i * a i ^ p) + ∑ i ∈ s, w i * b i := by
  calc
    _ ≤ ∑ i ∈ s, w i * (η ^ (1-p) * a i ^ p+b i) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (v24_min_power_with_error η (a i) (b i) p hη (ha i hi) (hb i hi) hp hp1) (hw i hi)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i hi; ring)

end OpenAI086
