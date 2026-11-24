import OpenAI086.PaperCubeEnergy

/-! The interval indicator has strictly positive U³ raw energy for L>0.
This closes the denominator issue, subject to kernel verification. It does
not assert a correlation with any structured nilsequence. -/
namespace OpenAI086
open scoped BigOperators

theorem v28_indicator_cube_positive (L : ℕ) [NeZero (16*L)] (hL : 0 < L) :
    0 < (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re := by
  classical
  let f := v27IntervalExtend L (fun _ => 1)
  let w : ZMod (16*L) → ℝ := fun x => if x.val < L then 1 else 0
  have hw (x : ZMod (16*L)) : 0 ≤ w x := by
    dsimp [w]; split <;> norm_num
  have hw0 : w 0 = 1 := by simp [w, hL]
  have hs : 1 ≤ ∑ x : ZMod (16*L), w x := by
    rw [← hw0]
    exact Finset.single_le_sum (fun x _ => hw x) (Finset.mem_univ 0)
  have hface (x : ZMod (16*L)) : v28Face f 0 0 x = (w x : ℂ) := by
    by_cases hx : x.val < L <;> simp [v28Face, f, v27IntervalExtend, w, hx]
  have hsface : 1 ≤ ‖∑ x : ZMod (16*L), v28Face f 0 0 x‖ := by
    have hcast : (∑ x : ZMod (16*L), (w x : ℂ)) = ((∑ x : ZMod (16*L), w x : ℝ) : ℂ) :=
      (map_sum Complex.ofRealHom w Finset.univ).symm
    simp only [hface]
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hs.trans (le_abs_self _)
  let E : ZMod (16*L) → ZMod (16*L) → ℝ :=
    fun a b => ‖∑ x : ZMod (16*L), v28Face f a b x‖^2
  have hE0 : 1 ≤ E 0 0 := by dsimp [E]; nlinarith [norm_nonneg (∑ x : ZMod (16*L), v28Face f 0 0 x)]
  have hE : 1 ≤ ∑ a : ZMod (16*L), ∑ b : ZMod (16*L), E a b := by
    calc
      1 ≤ E 0 0 := hE0
      _ ≤ ∑ b : ZMod (16*L), E 0 b :=
        Finset.single_le_sum (fun b _ => by dsimp [E]; positivity) (Finset.mem_univ 0)
      _ ≤ _ := Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => by dsimp [E]; positivity))
        (Finset.mem_univ 0)
  change 0 < (v27RawCube L f).re
  rw [v28_raw_cube_energy, Complex.ofReal_re]
  change 0 < (∑ a, ∑ b, E a b) / ((16*L : ℕ) : ℝ)^4
  have hN : 0 < (16*L : ℕ) := Nat.mul_pos (by decide) hL
  exact div_pos (lt_of_lt_of_le zero_lt_one hE) (pow_pos (by exact_mod_cast hN) 4)

theorem v28_interval_cube_nonnegative (L : ℕ) [NeZero (16*L)] (hL : 0 < L)
    (f : Fin L → ℂ) : 0 ≤ v27IntervalCubeRatio L f := by
  unfold v27IntervalCubeRatio
  exact div_nonneg (v28_raw_cube_nonnegative L _) (v28_indicator_cube_positive L hL).le

end OpenAI086
