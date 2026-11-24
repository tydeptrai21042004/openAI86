import OpenAI086.PaperCubeInterval

/-! Quantitative first reduction for the degree-two inverse input.
The normalized interval hypothesis implies a nontrivial second multiplicative
 derivative correlation. No nilsequence or frequency coherence is assumed.
This is an inverse-theorem component, not the Leng–Sah–Sawhney conclusion. -/
namespace OpenAI086
open scoped BigOperators

/-- A large cube energy forces a large individual second-derivative mean. -/
theorem v30_large_face_mean (L : ℕ) [NeZero (16*L)] (hL : 0 < L)
    (f : ZMod (16*L) → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hlarge : q^2 ≤ (v27RawCube L f).re) :
    ∃ a b : ZMod (16*L), q * ((16*L : ℕ) : ℝ) ≤
      ‖∑ x : ZMod (16*L), v28Face f a b x‖ := by
  classical
  let N : ℝ := ((16*L : ℕ) : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.mul_pos (by decide : 0 < 16) hL
  let E (a b : ZMod (16*L)) : ℝ := ‖∑ x, v28Face f a b x‖^2
  have hsum : q^2 * N^4 ≤ ∑ a, ∑ b, E a b := by
    rw [v28_raw_cube_energy, Complex.ofReal_re] at hlarge
    exact (le_div_iff₀ (pow_pos hN 4)).mp hlarge
  by_contra! h
  have hb (a b : ZMod (16*L)) : E a b < (q*N)^2 := by
    dsimp [E]
    have hh := h a b
    have hz := norm_nonneg (∑ x, v28Face f a b x)
    have hp := mul_pos (sub_pos.mpr hh) (show 0 < q*N + ‖∑ x, v28Face f a b x‖ by linarith)
    nlinarith
  have hrow (a : ZMod (16*L)) : (∑ b, E a b) < N * (q*N)^2 := by
    calc
      _ < ∑ _b : ZMod (16*L), (q*N)^2 := by
        apply Finset.sum_lt_sum
        · intro b _; exact (hb a b).le
        · exact ⟨0, Finset.mem_univ _, hb a 0⟩
      _ = _ := by simp [N, ZMod.card]
  have hall : (∑ a, ∑ b, E a b) < N * (N * (q*N)^2) := by
    calc
      _ < ∑ _a : ZMod (16*L), N * (q*N)^2 := by
        apply Finset.sum_lt_sum
        · intro a _; exact (hrow a).le
        · exact ⟨0, Finset.mem_univ _, hrow 0⟩
      _ = _ := by simp [N, ZMod.card]
  rw [show N * (N * (q*N)^2) = q^2*N^4 by ring] at hall
  exact (not_lt_of_ge hsum) hall

/-- Apply the preceding reduction to the actual interval-normalized U³
hypothesis. The denominator is positive by the existing indicator lemma. -/
theorem v30_interval_inverse_first_step (L : ℕ) [NeZero (16*L)] (hL : 0 < L)
    (f : Fin L → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hU : δ^8 ≤ v27IntervalCubeRatio L f) :
    ∃ a b : ZMod (16*L),
      δ^4 * Real.sqrt ((v27RawCube L (v27IntervalExtend L (fun _ => 1))).re) *
        ((16*L : ℕ) : ℝ) ≤
      ‖∑ x : ZMod (16*L), v28Face (v27IntervalExtend L f) a b x‖ := by
  let D := (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re
  have hD : 0 < D := v28_indicator_cube_positive L hL
  change δ^8 ≤ (v27RawCube L (v27IntervalExtend L f)).re / D at hU
  have h := (le_div_iff₀ hD).mp hU
  apply v30_large_face_mean L hL _ (δ^4 * Real.sqrt D) (by positivity)
  calc
    (δ^4 * Real.sqrt D)^2 = δ^8 * D := by
      rw [mul_pow, Real.sq_sqrt hD.le]; ring
    _ ≤ _ := h

/-- A density bound, applicable to normalized squared derivative means.
It is deliberately phrased in terms of the actual energy mass, not an
assumption that good shifts are uniformly distributed. -/
theorem v30_energy_good_count {I : Type*} [Fintype I] (u : I → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (hmean : η * (Fintype.card I : ℝ) ≤ ∑ i, u i) :
    η / 2 * (Fintype.card I : ℝ) ≤
      ((Finset.univ.filter (fun i => η/2 ≤ u i)).card : ℝ) := by
  classical
  let good := Finset.univ.filter (fun i : I => η/2 ≤ u i)
  have hs : (∑ i : I, u i) ≤ (∑ i : I, (if η/2 ≤ u i then (1 : ℝ) else 0) + η/2) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · linarith [(hu i).2]
    · linarith [lt_of_not_ge hi]
  have hcard : (∑ i : I, if η/2 ≤ u i then (1 : ℝ) else 0) = (good.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [good]
  rw [Finset.sum_add_distrib, hcard] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  change η / 2 * (Fintype.card I : ℝ) ≤ (good.card : ℝ)
  linarith

end OpenAI086
