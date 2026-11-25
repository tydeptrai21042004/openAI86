import OpenAI086.PaperV41Section3

/-! The two-window counterexample now uses the actual rational-height
predicate and exact qualifying scale set, not an abstract log-window
model. The corrected statement remains the intended formalization. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

def v42TwoFrequency (L : ℕ) (j : Fin 2) : ℝ :=
  if j = 0 then 1 else (2:ℝ)^(3*L)

/-- Each coordinate magnitude really belongs to the paper's finite set E
at height B=2, witnessed by the corresponding unit rational vector. -/
theorem v42_coordinate_height (L : ℕ) (i : Fin 2) :
    v34HeightValue 2 2 (v42TwoFrequency L) (v42TwoFrequency L i) := by
  have hi : 0 < v42TwoFrequency L i := by
    unfold v42TwoFrequency
    split <;> positivity
  refine ⟨hi, (fun j => if j = i then 1 else 0), (fun _ => 1), ?_, ?_, ?_⟩
  · intro j; split <;> norm_num
  · intro j; norm_num
  · unfold v34Eval
    simp only [Nat.cast_one]
    have he : (∑ j : Fin 2, (((if j = i then 1 else 0 : ℤ):ℝ)/(1:ℝ))*v42TwoFrequency L j) =
        v42TwoFrequency L i := by
      classical
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji; simp [hji]
      · simp
    rw [he, abs_of_pos hi]

theorem v42_one_height (L : ℕ) : v34HeightValue 2 2 (v42TwoFrequency L) 1 := by
  simpa [v42TwoFrequency] using v42_coordinate_height L (0 : Fin 2)

theorem v42_large_height (L : ℕ) :
    v34HeightValue 2 2 (v42TwoFrequency L) ((2:ℝ)^(3*L)) := by
  simpa [v42TwoFrequency] using v42_coordinate_height L (1 : Fin 2)

/-- Exact transfer of each log window into the qualifying scales at
r0=alpha=1, beta=2^L and ell=1. -/
theorem v42_window_is_qualifying (L : ℕ) (n : ℤ) (k : ℕ)
    (hw : v31LogWindow (k:ℤ) n L) :
    1 ≤ v35Scale 1 1 n*(2:ℝ)^k ∧ v35Scale 1 1 n*(2:ℝ)^k ≤ (2:ℝ)^L := by
  have hb : (1:ℝ) ≤ (2:ℝ)^L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  apply (v36_scale_iff_window 1 1 ((2:ℝ)^L) ((2:ℝ)^k) 1 n
    (by norm_num) (by norm_num) hb (by positivity) (by norm_num)).mpr
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (0:ℝ) ≤ (k:ℝ)-(n:ℝ) := by exact_mod_cast hw.1
  have h2 : (k:ℝ)-(n:ℝ) ≤ (L:ℝ) := by exact_mod_cast hw.2
  unfold v36ScaleLo v36ScaleHi
  simp only [Nat.cast_one, Real.log_one, mul_zero, zero_add, sub_zero, one_mul, Real.log_pow]
  constructor
  · apply (div_le_iff₀ hlog).mpr
    nlinarith [mul_le_mul_of_nonneg_right h2 hlog.le]
  · apply (le_div_iff₀ hlog).mpr
    nlinarith [mul_nonneg h1 hlog.le]

/-- For any fixed additive natural bound K, the *actual* qualifying
set exceeds K+L+1. This refutes the printed coefficient-one estimate
with d=B=2, even though the frequency vector is finite dimensional. -/
theorem v42_actual_height_obstruction (K : ℕ) :
    ∃ L : ℕ, K+L+1 <
      (v36Qualifying (v34Values 2 2 (v42TwoFrequency L)) 1 1 ((2:ℝ)^L) 1).card := by
  classical
  obtain ⟨L,S,hcard,hw⟩ := v31_no_dimension_free_width K
  refine ⟨L, hcard.trans_le (Finset.card_le_card ?_)⟩
  intro n hn
  have hb : (1:ℝ) ≤ (2:ℝ)^L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  apply (v36_mem_qualifying _ _ _ _ _ _
    (fun v hv => ((v34_mem_values 2 2 (v42TwoFrequency L) v).mp hv).1)
    (by norm_num) (by norm_num) hb (by norm_num)).mpr
  rcases hw n hn with h | h
  · refine ⟨1,(v34_mem_values _ _ _ _).mpr (v42_one_height L),?_⟩
    simpa using v42_window_is_qualifying L n 0 (by simpa using h)
  · refine ⟨(2:ℝ)^(3*L),(v34_mem_values _ _ _ _).mpr (v42_large_height L),?_⟩
    exact v42_window_is_qualifying L n (3*L) (by simpa using h)

end OpenAI086
