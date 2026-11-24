import Mathlib

/-! Section 10.2, p.91: three square budgets imply powered summability
for p >= 2/3, with no dependence on the number of terms. The actual
construction of the side factors and their budgets remains open. -/
namespace OpenAI086

/-- A normalized three-side estimate. The factor 3 in the final sum is
harmless for the paper's polynomial budget. A fourth uniformly bounded
factor may be accounted for separately. -/
theorem v39_three_side_pointwise (a b c p : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1)
    (hp : 2/3 ≤ p) : (a*b*c)^p ≤ a^2+b^2+c^2 := by
  let m := max a (max b c)
  have ham : a ≤ m := le_max_left _ _
  have hbm : b ≤ m := (le_max_left b c).trans (le_max_right a (max b c))
  have hcm : c ≤ m := (le_max_right b c).trans (le_max_right a (max b c))
  have hm : 0 ≤ m := ha.trans ham
  have hm1 : m ≤ 1 := max_le ha1 (max_le hb1 hc1)
  have hp0 : 0 < p := by linarith
  by_cases hz : m = 0
  · have hae : a = 0 := le_antisymm (ham.trans_eq hz) ha
    rw [hae]
    simp [Real.zero_rpow (ne_of_gt hp0)] <;> positivity
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    have hprod : a*b*c ≤ m*m*m := by
      exact mul_le_mul (mul_le_mul ham hbm hb hm) hcm hc (mul_nonneg hm hm)
    have hpow := Real.rpow_le_rpow (mul_nonneg (mul_nonneg ha hb) hc) hprod hp0.le
    have hid : (m*m*m)^p = m^(3*p) := by
      rw [Real.mul_rpow (mul_nonneg hm hm) hm, Real.mul_rpow hm hm,
        ← Real.rpow_add hmpos, ← Real.rpow_add hmpos]
      congr 1 <;> ring
    rw [hid] at hpow
    have he : 0 ≤ 3*p-2 := by linarith
    have hsmall : m^(3*p-2) ≤ 1 := by
      simpa using Real.rpow_le_rpow hm hm1 he
    have hr : m^(3*p) ≤ m^2 := by
      calc
        _ = m^(2:ℝ)*m^(3*p-2) := by rw [← Real.rpow_add hmpos]; congr 1 <;> ring
        _ ≤ m^(2:ℝ)*1 := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hm _)
        _ = m^2 := by rw [mul_one, Real.rpow_two]
    have hs : m^2 ≤ a^2+b^2+c^2 := by
      dsimp [m]
      rcases le_total a (max b c) with h | h
      · rw [max_eq_right h]
        rcases le_total b c with hbc | hbc
        · rw [max_eq_right hbc]; nlinarith [sq_nonneg a, sq_nonneg b]
        · rw [max_eq_left hbc]; nlinarith [sq_nonneg a, sq_nonneg c]
      · rw [max_eq_left h]; nlinarith [sq_nonneg b, sq_nonneg c]
    exact (hpow.trans hr).trans hs

/-- Powered summation with actual finite square budgets, no bound on
the cardinality of s. Pointwise normalization follows from each budget. -/
theorem v39_three_side_square_budget {I : Type*} (s : Finset I)
    (a b c : I → ℝ) (p : ℝ) (hp : 2/3 ≤ p)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hA : (∑ i ∈ s, (a i)^2) ≤ 1)
    (hB : (∑ i ∈ s, (b i)^2) ≤ 1)
    (hC : (∑ i ∈ s, (c i)^2) ≤ 1) :
    (∑ i ∈ s, (a i*b i*c i)^p) ≤ 3 := by
  classical
  have hnorm (f : I → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
      (hF : (∑ i ∈ s, (f i)^2) ≤ 1) : ∀ i ∈ s, f i ≤ 1 := by
    intro i hi
    have h := (Finset.single_le_sum (fun j _ => sq_nonneg (f j)) hi).trans hF
    nlinarith [hf i hi, sq_nonneg (f i-1)]
  calc
    _ ≤ ∑ i ∈ s, ((a i)^2+(b i)^2+(c i)^2) := Finset.sum_le_sum
      (fun i hi => v39_three_side_pointwise (a i) (b i) (c i) p
        (ha i hi) (hb i hi) (hc i hi) (hnorm a ha hA i hi)
        (hnorm b hb hB i hi) (hnorm c hc hC i hi) hp)
    _ ≤ 3 := by simp only [Finset.sum_add_distrib]; linarith

/-- Rescale arbitrary positive square-size budgets to the normalized
case. The bound is 3*(A B C)^p, with A,B,C the respective L² budgets.
The fourth role can be handled by a pointwise factor before this sum. -/
theorem v39_three_side_scaled_budget {I : Type*} (s : Finset I)
    (a b c : I → ℝ) (A B C p : ℝ) (hp : 2/3 ≤ p)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (ha2 : (∑ i ∈ s, (a i)^2) ≤ A^2)
    (hb2 : (∑ i ∈ s, (b i)^2) ≤ B^2)
    (hc2 : (∑ i ∈ s, (c i)^2) ≤ C^2) :
    (∑ i ∈ s, (a i*b i*c i)^p) ≤ 3*(A*B*C)^p := by
  classical
  have hnorm (f : I → ℝ) (F : ℝ) (hF : 0 < F)
      (hf : (∑ i ∈ s, (f i)^2) ≤ F^2) :
      (∑ i ∈ s, (f i/F)^2) ≤ 1 := by
    simp only [div_pow, ← Finset.sum_div]
    exact (div_le_iff₀ (sq_pos_of_pos hF)).mpr (by simpa using hf)
  have h := v39_three_side_square_budget s (fun i => a i/A)
    (fun i => b i/B) (fun i => c i/C) p hp
    (fun i hi => div_nonneg (ha i hi) hA.le)
    (fun i hi => div_nonneg (hb i hi) hB.le)
    (fun i hi => div_nonneg (hc i hi) hC.le)
    (hnorm a A hA ha2) (hnorm b B hB hb2) (hnorm c C hC hc2)
  have hABC : 0 < A*B*C := mul_pos (mul_pos hA hB) hC
  calc
    _ = (A*B*C)^p * (∑ i ∈ s, ((a i/A)*(b i/B)*(c i/C))^p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hn : 0 ≤ (a i/A)*(b i/B)*(c i/C) :=
        mul_nonneg (mul_nonneg (div_nonneg (ha i hi) hA.le) (div_nonneg (hb i hi) hB.le))
          (div_nonneg (hc i hi) hC.le)
      rw [← Real.mul_rpow hABC.le hn]
      congr 1
      field_simp [hA.ne', hB.ne', hC.ne'] <;> ring
    _ ≤ (A*B*C)^p * 3 := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hABC.le _)
    _ = _ := by ring

end OpenAI086
