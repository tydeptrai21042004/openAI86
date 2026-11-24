import OpenAI086.PaperInverseExtremal
import OpenAI086.PaperInverseDerivative

/-! Uniform normalization for the actual interval U³ domain. A box of
ceil(L/4)^4 supported cubes gives D ≥ 64^(-4), eliminating the length
loss in V30's first inverse step. This is not the general inverse theorem. -/
namespace OpenAI086
open scoped BigOperators

/-- A finite collection on which a nonnegative weight is one contributes
at least its cardinality to the full mass. -/
theorem v31_box_mass {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∀ i, w (e i) = 1) : (Fintype.card I : ℝ) ≤ ∑ j, w j := by
  classical
  calc
    (Fintype.card I : ℝ) = ∑ i : I, w (e i) := by simp [he]
    _ = ∑ j ∈ (Finset.univ : Finset I).map e, w j := by rw [Finset.sum_map]
    _ ≤ ∑ j, w j := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun j _ _ => hw j)

/-- Explicit embedding of the short integer interval into the cyclic group. -/
def v31SmallEmbedding (L K : ℕ) [NeZero (16*L)] (hK : K ≤ 16*L) :
    Fin K ↪ ZMod (16*L) where
  toFun i := (i.val : ZMod (16*L))
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi : i.val < 16*L := lt_of_lt_of_le i.isLt hK
    have hj : j.val < 16*L := lt_of_lt_of_le j.isLt hK
    simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using
      congrArg ZMod.val hij

/-- All eight vertices of the positive short cube stay in the interval. -/
theorem v31_short_cube_supported (L K : ℕ) [NeZero (16*L)]
    (hL : 0 < L) (hK : 4*K ≤ L+3)
    (x : Fin K) (h : Fin 3 → Fin K) (ω : Fin 3 → Fin 2) :
    (v30Vertex L (x.val : ZMod (16*L))
      (fun i => (h i).val) ω).val < L := by
  let n := x.val + ∑ i : Fin 3, (ω i).val * (h i).val
  have hb (i : Fin 3) : (ω i).val * (h i).val < K := by
    have hv := (ω i).isLt
    have hh := (h i).isLt
    have he : (ω i).val = 0 ∨ (ω i).val = 1 := by omega
    rcases he with he | he <;> simp [he] <;> omega
  have hn : n < L := by
    dsimp [n]
    rw [Fin.sum_univ_three]
    have hx := x.isLt
    have h0 := hb 0
    have h1 := hb 1
    have h2 := hb 2
    omega
  have hv : v30Vertex L (x.val : ZMod (16*L))
      (fun i => (h i).val) ω = (n : ZMod (16*L)) := by
    simp only [v30Vertex, n, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
  rw [hv, ZMod.val_natCast_of_lt (by omega)]
  exact hn

/-- The indicator's raw U³ energy is the normalized count of supported
cubes. This connects the actual V27 raw definition to the V30 mask. -/
theorem v31_indicator_mask_sum (L : ℕ) [NeZero (16*L)] :
    (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re =
      (∑ x : ZMod (16*L), ∑ h : Fin 3 → ZMod (16*L), v30CubeMask L x h) /
        ((16*L : ℕ) : ℝ)^4 := by
  have hc : v27RawCube L (v27IntervalExtend L (fun _ => 1)) =
      (((∑ x : ZMod (16*L), ∑ h : Fin 3 → ZMod (16*L), v30CubeMask L x h) /
        ((16*L : ℕ) : ℝ)^4 : ℝ) : ℂ) := by
    push_cast
    change (∑ x : ZMod (16*L), ∑ h : Fin 3 → ZMod (16*L),
      v30CubeTerm L (fun _ => 1) x h) / _ = _
    simp only [v30_indicator_term]
  rw [hc, Complex.ofReal_re]

/-- Uniform lower bound independent of interval length, for the actual
normalization denominator used by Theorem 4.7's formalization. -/
theorem v31_indicator_cube_uniform (L : ℕ) [NeZero (16*L)] (hL : 0 < L) :
    (1:ℝ)/64^4 ≤ (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re := by
  classical
  let K := (L+3)/4
  have hK : 4*K ≤ L+3 := by dsimp [K]; omega
  have hKlo : L ≤ 4*K := by dsimp [K]; omega
  have hKb : K ≤ 16*L := by omega
  let G := ZMod (16*L)
  let e := v31SmallEmbedding L K hKb
  let eh : (Fin 3 → Fin K) ↪ (Fin 3 → G) :=
    ⟨fun h i => e (h i), by intro a b he; funext i; exact e.injective (congrFun he i)⟩
  let E : (Fin K × (Fin 3 → Fin K)) ↪ (G × (Fin 3 → G)) :=
    ⟨fun p => (e p.1, eh p.2), by
      intro a b hab
      exact Prod.ext (e.injective (congrArg Prod.fst hab))
        (eh.injective (congrArg Prod.snd hab))⟩
  let w : G × (Fin 3 → G) → ℝ := fun p => v30CubeMask L p.1 p.2
  have hw (p : G × (Fin 3 → G)) : 0 ≤ w p := by
    dsimp [w, v30CubeMask]; split <;> norm_num
  have he (p : Fin K × (Fin 3 → Fin K)) : w (E p) = 1 := by
    change v30CubeMask L (p.1.val : G) (fun i => (p.2 i).val) = 1
    unfold v30CubeMask
    rw [if_pos (v31_short_cube_supported L K hL hK p.1 p.2)]
  have hm := v31_box_mass E w hw he
  have hmass : (K:ℝ)^4 ≤ ∑ x : G, ∑ h : Fin 3 → G, v30CubeMask L x h := by
    simpa [w, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fun, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hm
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hkR : (L:ℝ) ≤ 4*(K:ℝ) := by exact_mod_cast hKlo
  have hp : ((L:ℝ)/4)^4 ≤ (K:ℝ)^4 := by
    gcongr <;> linarith
  rw [v31_indicator_mask_sum]
  have hN : (0:ℝ) < ((16*L:ℕ):ℝ)^4 := by positivity
  apply (le_div_iff₀ hN).2
  calc
    _ = ((L:ℝ)/4)^4 := by push_cast; ring
    _ ≤ (K:ℝ)^4 := hp
    _ ≤ _ := hmass

/-- A length-independent inverse first step: some second derivative has
normalized mean at least δ⁴/4096. The remaining coherence and nilsequence
construction are not consequences of this estimate alone. -/
theorem v31_uniform_inverse_first_step (L : ℕ) [NeZero (16*L)] (hL : 0 < L)
    (f : Fin L → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hU : δ^8 ≤ v27IntervalCubeRatio L f) :
    ∃ a b : ZMod (16*L), (δ^4/4096)*((16*L : ℕ):ℝ) ≤
      ‖∑ x : ZMod (16*L), v28Face (v27IntervalExtend L f) a b x‖ := by
  let D := (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re
  have hD : 0 < D := v28_indicator_cube_positive L hL
  change δ^8 ≤ (v27RawCube L (v27IntervalExtend L f)).re / D at hU
  have h := (le_div_iff₀ hD).mp hU
  have hlow : (1:ℝ)/64^4 ≤ D := v31_indicator_cube_uniform L hL
  apply v30_large_face_mean L hL _ (δ^4/4096) (by positivity)
  calc
    (δ^4/4096)^2 = δ^8*(1/64^4) := by ring
    _ ≤ δ^8*D := mul_le_mul_of_nonneg_left hlow (by positivity)
    _ ≤ _ := h

end OpenAI086
