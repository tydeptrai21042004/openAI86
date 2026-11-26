import TrilinearHT.Auto.Sec16_3SummingUpdateLevels

/-! Sections 7.7 and 10.3: explicit paper parameter reserve. The near-band
cost stays at power one, not the exponent used for the three-side terms. -/
namespace OpenAI086.ReferenceV67
open Auto

/-- The exact arithmetic of the gain in the paper's Section 10.3. -/
theorem near_gain {P K G₀ a : ℝ} (hP : 1 ≤ P) (hK : 0 ≤ K) (hG : 0 ≤ G₀)
    (hG8 : G₀ ≤ P ^ (1 / 8 : ℝ)) (hKa : (K + 2) ^ a ≤ P ^ (1 / 8 : ℝ)) :
    G₀ * (K + 2) ^ a / Real.sqrt P ≤ P ^ (-(1 / 4) : ℝ) := by
  have hP0 : 0 < P := by linarith
  have hsq : (Real.sqrt P)⁻¹ = P ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hP0.le]
  have hm := mul_le_mul hG8 hKa (Real.rpow_nonneg (by linarith : 0 ≤ K + 2) a)
    (Real.rpow_nonneg hP0.le _)
  rw [div_eq_mul_inv, hsq]
  calc _ ≤ (P ^ (1 / 8 : ℝ) * P ^ (1 / 8 : ℝ)) * P ^ (-(1 / 2) : ℝ) :=
      mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hP0.le _)
    _ = _ := by rw [← Real.rpow_add hP0, ← Real.rpow_add hP0]; norm_num

/-- A polynomial depth-block bound and small `q-2` imply the numerical
reserve for the paper exponent, rather than only for the reference exponent. -/
theorem depth_power_reserve {P K C₅ C₁₉ q : ℝ} (hP : 1 ≤ P) (hK : 0 ≤ K)
    (hC : 0 ≤ C₁₉) (hq : 2 ≤ q) (hpoly : K + 2 ≤ P ^ C₅)
    (hsmall : C₅ * (C₁₉ * (q - 2)) ≤ 1 / 8) :
    (K + 2) ^ (C₁₉ * (q - 2)) ≤ P ^ (1 / 8 : ℝ) := by
  have hP0 : 0 ≤ P := by linarith
  calc _ ≤ (P ^ C₅) ^ (C₁₉ * (q - 2)) :=
      Real.rpow_le_rpow (by linarith) hpoly (mul_nonneg hC (sub_nonneg.mpr hq))
    _ = P ^ (C₅ * (C₁₉ * (q - 2))) := by rw [Real.rpow_mul hP0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hsmall

/-- Full absolute near-band scalar gain with the finite-depth constant
retained. This does not prove the analytic overhead bound itself. -/
theorem absolute_near_gain {P K G₀ C₅ C₁₉ q CN Cq R : ℝ}
    (hP : 1 ≤ P) (hK : 0 ≤ K) (hG : 0 ≤ G₀) (hG8 : G₀ ≤ P ^ (1 / 8 : ℝ))
    (hC : 0 ≤ C₁₉) (hq : 2 ≤ q) (hpoly : K + 2 ≤ P ^ C₅)
    (hsmall : C₅ * (C₁₉ * (q - 2)) ≤ 1 / 8)
    (hCN : 0 ≤ CN) (hCq : 0 ≤ Cq) (hR : 0 ≤ R) :
    (1 + CN) * Cq * (G₀ * (K + 2) ^ (C₁₉ * (q - 2)) / Real.sqrt P) * R ≤
      (1 + CN) * Cq * P ^ (-(1 / 4) : ℝ) * R := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (near_gain hP hK hG hG8 (depth_power_reserve hP hK hC hq hpoly hsmall))
      (mul_nonneg (by linarith) hCq)) hR

end OpenAI086.ReferenceV67
#print axioms OpenAI086.ReferenceV67.near_gain
#print axioms OpenAI086.ReferenceV67.depth_power_reserve
#print axioms OpenAI086.ReferenceV67.absolute_near_gain
