import TrilinearHT.Auto.Sec16_2QuantitativeInequality

/-! The finite count of all reference first-top stopping tests and its
contribution to the polynomial reserve of Sections 8.10 and 10.3. -/
namespace OpenAI086.ReferenceV69
open Auto
open scoped BigOperators

open Classical in
theorem top_test_card {D U H : ℝ} (hD : 2 ≤ D) (hU : D⁻¹ ≤ U)
    (J : ℕ) (hH : 1 ≤ H) (hJ : (J : ℝ) + 1 ≤ H)
    (hT : (Nat.log 2 ⌊D⌋₊ : ℝ) + 1 ≤ H)
    (hL : Real.logb 2 U - Real.logb 2 D⁻¹ + 3 ≤ H) :
    (((Finset.range (J+1)) ×ˢ
      (((Finset.range (Nat.log 2 ⌊D⌋₊ + 1)) ×ˢ (Finset.range (Nat.log 2 ⌊D⌋₊ + 1))) ×ˢ
      dyThr D⁻¹ U D)).card : ℝ) ≤ H ^ 4 := by
  have hDp : 0 < D := by linarith
  have hInv : 0 < D⁻¹ := inv_pos.mpr hDp
  have hcard := (dyThr_spec hInv hU hU).2.2.2.trans hL
  simp only [Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ H * ((H * H) * H) := by gcongr
    _ = H ^ 4 := by ring

/-- Collect the actual reference coefficient 24(2G0+2 K V0)N/ρ into
one polynomial reserve, assuming all the normalized budgets are bounded. -/
theorem first_top_polynomial {G0 V0 K N ρ H : ℝ} (hH : 1 ≤ H)
    (hG0 : 0 ≤ G0) (hV0 : 0 ≤ V0) (hK : 0 ≤ K) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (hG : G0 ≤ H) (hV : V0 ≤ H) (hKH : K ≤ H)
    (hNH : N ≤ H ^ 4) (hρH : ρ⁻¹ ≤ H) :
    24 * (2 * G0 + 2 * K * V0) * N / ρ ≤ 96 * H ^ 7 := by
  have hH0 : 0 ≤ H := by linarith
  have hHH : H ≤ H ^ 2 := by nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hH)]
  have hbase : 2 * G0 + 2 * K * V0 ≤ 4 * H ^ 2 := by
    have hk : K * V0 ≤ H * H := by gcongr
    nlinarith
  rw [div_eq_mul_inv]
  calc
    _ ≤ 24 * (4 * H ^ 2) * H ^ 4 * H := by gcongr
    _ = 96 * H ^ 7 := by ring

end OpenAI086.ReferenceV69
#print axioms OpenAI086.ReferenceV69.top_test_card
#print axioms OpenAI086.ReferenceV69.first_top_polynomial
