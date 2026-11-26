import ReferenceV70PaperTypes
import TrilinearHT.Auto.Sec16_2QuantitativeInequality

/-! Section 8.10 / 10.3: the type range and the number of stopping tests
for the printed base-1.1 type classes, not the reference dyadic classes.
The estimate counts a finite superset of all possible tests; it does not
supply the analytic first-top energy bound for those classes. -/
namespace OpenAI086.ReferenceV70
open Auto OpenAI086.AdaptedV56
open scoped BigOperators

/-- Every positive count bounded by D has a type in the printed range. -/
theorem paper_type_mem {n D : ℕ} (hn : n ≤ D) :
    v57FloorLog n ∈ Finset.range (v57FloorLog D+1) := by
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (v57_floorLog_mono hn))

/-- The number of possible type indices is logarithmic in D. -/
theorem paper_type_range_le {D : ℝ} (hD : 2 ≤ D) :
    ((Finset.range (v57FloorLog ⌊D⌋₊+1)).card : ℝ) ≤
      Real.log D / Real.log (11/10:ℝ) + 1 := by
  have hD0 : 0 ≤ D := by linarith
  have hDf : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD0
  have hDn : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hn1 : (1:ℝ) ≤ (⌊D⌋₊:ℕ) := by exact_mod_cast hDn
  have hb : 0 < Real.log (11/10:ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (⌊D⌋₊:ℕ) ≤ Real.log D :=
    Real.log_le_log (by linarith) hDf
  have hfloor : (v57FloorLog ⌊D⌋₊ : ℝ) ≤
      Real.log (⌊D⌋₊:ℕ) / Real.log (11/10:ℝ) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hn1) hb.le)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one]
  exact add_le_add_right (hfloor.trans (div_le_div_of_nonneg_right hlog hb.le)) _

/-- Paper type pair, height and amplitude-threshold count; both type
coordinates have the base-1.1 cardinality, not a dyadic proxy. -/
open Classical in
theorem paper_top_test_card {D U H : ℝ} (hD : 2 ≤ D) (hU : D⁻¹ ≤ U)
    (J : ℕ) (hH : 1 ≤ H) (hJ : (J:ℝ)+1 ≤ H)
    (hT : Real.log D / Real.log (11/10:ℝ) + 1 ≤ H)
    (hL : Real.logb 2 U - Real.logb 2 D⁻¹ + 3 ≤ H) :
    (((Finset.range (J+1)) ×ˢ
      (((Finset.range (v57FloorLog ⌊D⌋₊+1)) ×ˢ
        (Finset.range (v57FloorLog ⌊D⌋₊+1))) ×ˢ dyThr D⁻¹ U D)).card : ℝ) ≤ H^4 := by
  have hInv : 0 < D⁻¹ := inv_pos.mpr (by linarith)
  have ht := (paper_type_range_le hD).trans hT
  have hl := (dyThr_spec hInv hU hU).2.2.2.trans hL
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at ht
  simp only [Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ H * ((H*H)*H) := by gcongr
    _ = H^4 := by ring

end OpenAI086.ReferenceV70
#print axioms OpenAI086.ReferenceV70.paper_type_mem
#print axioms OpenAI086.ReferenceV70.paper_type_range_le
#print axioms OpenAI086.ReferenceV70.paper_top_test_card
