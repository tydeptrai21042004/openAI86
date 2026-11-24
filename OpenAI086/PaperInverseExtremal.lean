import OpenAI086.PaperCubeInterval

/-! Endpoint inverse theorem on the actual interval: at normalized U³=1,
all supported cubes saturate, giving a quadratic phase with perfect correlation.
This does not handle the quantitative inverse theorem at 0 < δ < 1. -/
namespace OpenAI086
open scoped BigOperators

noncomputable def v30Vertex (L : ℕ) (x : ZMod (16*L))
    (h : Fin 3 → ZMod (16*L)) (ω : Fin 3 → Fin 2) : ZMod (16*L) :=
  x + ∑ i : Fin 3, ((ω i).val : ZMod (16*L))*h i

noncomputable def v30CubeFactor (L : ℕ) (f : Fin L → ℂ)
    (x : ZMod (16*L)) (h : Fin 3 → ZMod (16*L)) (ω : Fin 3 → Fin 2) : ℂ :=
  let z := v27IntervalExtend L f (v30Vertex L x h ω)
  if (∑ i : Fin 3, (ω i).val) % 2 = 0 then z else star z

noncomputable def v30CubeTerm (L : ℕ) (f : Fin L → ℂ)
    (x : ZMod (16*L)) (h : Fin 3 → ZMod (16*L)) : ℂ :=
  ∏ ω : Fin 3 → Fin 2, v30CubeFactor L f x h ω

noncomputable def v30CubeMask (L : ℕ) (x : ZMod (16*L))
    (h : Fin 3 → ZMod (16*L)) : ℝ := by
  classical
  exact if ∀ ω : Fin 3 → Fin 2, (v30Vertex L x h ω).val < L then 1 else 0

theorem v30_factor_norm_le_one (L : ℕ) (f : Fin L → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (x : ZMod (16*L))
    (h : Fin 3 → ZMod (16*L)) (ω : Fin 3 → Fin 2) :
    ‖v30CubeFactor L f x h ω‖ ≤ 1 := by
  have hb : ‖v27IntervalExtend L f (v30Vertex L x h ω)‖ ≤ 1 := by
    unfold v27IntervalExtend
    split
    · exact hf _
    · simp
  unfold v30CubeFactor
  dsimp only
  split
  · exact hb
  · simpa using hb

theorem v30_indicator_term (L : ℕ) (x : ZMod (16*L))
    (h : Fin 3 → ZMod (16*L)) :
    v30CubeTerm L (fun _ => 1) x h = (v30CubeMask L x h : ℂ) := by
  classical
  by_cases hs : ∀ ω : Fin 3 → Fin 2, (v30Vertex L x h ω).val < L
  · simp [v30CubeTerm, v30CubeMask, v30CubeFactor, v27IntervalExtend, hs]
  · push_neg at hs
    obtain ⟨ω, hω⟩ := hs
    have hz : v30CubeFactor L (fun _ => 1) x h ω = 0 := by
      simp [v30CubeFactor, v27IntervalExtend, not_lt.mpr hω]
    have hns : ¬ ∀ ω : Fin 3 → Fin 2, (v30Vertex L x h ω).val < L :=
      fun ht => (not_lt.mpr hω) (ht ω)
    simp [v30CubeTerm, v30CubeMask, hns, Finset.prod_eq_zero (Finset.mem_univ ω) hz]

theorem v30_term_norm_le_mask (L : ℕ) (f : Fin L → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (x : ZMod (16*L))
    (h : Fin 3 → ZMod (16*L)) :
    ‖v30CubeTerm L f x h‖ ≤ v30CubeMask L x h := by
  classical
  by_cases hs : ∀ ω : Fin 3 → Fin 2, (v30Vertex L x h ω).val < L
  · rw [v30CubeMask, if_pos hs, v30CubeTerm, norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => v30_factor_norm_le_one L f hf x h i)
  · have hns := hs
    push_neg at hs
    obtain ⟨ω, hω⟩ := hs
    have hz : v30CubeFactor L f x h ω = 0 := by
      simp [v30CubeFactor, v27IntervalExtend, not_lt.mpr hω]
    rw [v30CubeMask, if_neg hns, v30CubeTerm, Finset.prod_eq_zero (Finset.mem_univ ω) hz]
    simp

/-- Equality of sums of nonnegative deficits forces each deficit to vanish. -/
theorem v30_zero_deficit {I : Type*} [Fintype I] (d : I → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 0) (i : I) : d i = 0 := by
  have h := Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  rw [hs] at h
  exact le_antisymm h (hd i)

/-- The only point in the closed complex unit disk with real part one is one. -/
theorem v30_unit_disk_real_one (z : ℂ) (hn : ‖z‖ ≤ 1) (hr : z.re = 1) : z = 1 := by
  have hs : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr] at hs
  have hi : z.im = 0 := by nlinarith [sq_nonneg z.im]
  apply Complex.ext <;> simp [hr, hi]

/-- Extremal normalized cube ratio forces each supported cube term to be one.
The hypothesis is exactly the ratio in the existing paper domain, not a
surrogate recurrence assumption. -/
theorem v30_maximal_cube_terms (L : ℕ) [NeZero (16*L)] (hL : 0 < L)
    (f : Fin L → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1)
    (hU : v27IntervalCubeRatio L f = 1)
    (x : ZMod (16*L)) (h : Fin 3 → ZMod (16*L))
    (hs : ∀ ω : Fin 3 → Fin 2, (v30Vertex L x h ω).val < L) :
    v30CubeTerm L f x h = 1 := by
  classical
  let G := ZMod (16*L)
  let D := (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re
  have hD : 0 < D := v28_indicator_cube_positive L hL
  have hre : (v27RawCube L (v27IntervalExtend L f)).re = D := by
    change (v27RawCube L (v27IntervalExtend L f)).re / D = 1 at hU
    have hh := (div_eq_iff hD.ne').mp hU
    simpa using hh
  have hraw : v27RawCube L (v27IntervalExtend L f) =
      v27RawCube L (v27IntervalExtend L (fun _ => 1)) := by
    apply Complex.ext
    · exact hre
    · rw [v28_raw_cube_real, v28_raw_cube_real]
  let N : ℂ := ((16*L : ℕ) : ℂ)^4
  have hN : N ≠ 0 := by
    dsimp [N]
    have hpos : 0 < 16*L := Nat.mul_pos (by decide) hL
    exact pow_ne_zero 4 (by exact_mod_cast (ne_of_gt hpos))
  have hnum : (∑ y : G, ∑ k : Fin 3 → G, v30CubeTerm L f y k) =
      ∑ y : G, ∑ k : Fin 3 → G, v30CubeTerm L (fun _ => 1) y k := by
    have hh : (∑ y : G, ∑ k : Fin 3 → G, v30CubeTerm L f y k) / N =
        (∑ y : G, ∑ k : Fin 3 → G, v30CubeTerm L (fun _ => 1) y k) / N := hraw
    have hh' := congrArg (fun z : ℂ => z * N) hh
    simpa [div_mul_cancel₀ _ hN] using hh'
  let d (y : G) (k : Fin 3 → G) := v30CubeMask L y k - (v30CubeTerm L f y k).re
  have hd (y : G) (k : Fin 3 → G) : 0 ≤ d y k :=
    sub_nonneg.mpr ((Complex.re_le_norm _).trans (v30_term_norm_le_mask L f hf y k))
  have hsum : (∑ y : G, ∑ k : Fin 3 → G, d y k) = 0 := by
    have hh := congrArg Complex.re hnum
    simp only [map_sum, Complex.sum_re, v30_indicator_term, Complex.ofReal_re] at hh
    dsimp [d]
    simp only [Finset.sum_sub_distrib]
    linarith
  have hrow : (∑ k : Fin 3 → G, d x k) = 0 :=
    v30_zero_deficit (fun y : G => ∑ k : Fin 3 → G, d y k)
      (fun y => Finset.sum_nonneg (fun k _ => hd y k)) hsum x
  have hx := v30_zero_deficit (d x) (hd x) hrow h
  have hm : v30CubeMask L x h = 1 := by simp [v30CubeMask, hs]
  apply v30_unit_disk_real_one
  · simpa [hm] using v30_term_norm_le_mask L f hf x h
  · dsimp [d] at hx; linarith

/-- A supported saturated cube cannot contain a non-unit-modulus factor. -/
theorem v30_saturated_factor (L : ℕ) (f : Fin L → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (x : ZMod (16*L)) (h : Fin 3 → ZMod (16*L))
    (heq : v30CubeTerm L f x h = 1) (ω : Fin 3 → Fin 2) :
    ‖v30CubeFactor L f x h ω‖ = 1 := by
  classical
  have hprod : (∏ v : Fin 3 → Fin 2, ‖v30CubeFactor L f x h v‖) = 1 := by
    rw [← norm_prod, ← v30CubeTerm, heq, norm_one]
  let S := (Finset.univ : Finset (Fin 3 → Fin 2)).erase ω
  have hrest : (∏ v ∈ S, ‖v30CubeFactor L f x h v‖) ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => v30_factor_norm_le_one L f hf x h i)
  have he : (∏ v ∈ S, ‖v30CubeFactor L f x h v‖) * ‖v30CubeFactor L f x h ω‖ = 1 := by
    rw [show S = Finset.univ.erase ω from rfl, Finset.prod_erase_mul _ _ (Finset.mem_univ ω), hprod]
  have hh := mul_le_mul_of_nonneg_right hrest (norm_nonneg (v30CubeFactor L f x h ω))
  rw [he, one_mul] at hh
  exact le_antisymm (v30_factor_norm_le_one L f hf x h ω) hh


/-- Natural labels inside [0,L) are unchanged by the cyclic embedding. -/
theorem v30_interval_cast (L : ℕ) (f : Fin L → ℂ) (n : ℕ) (hn : n < L) :
    v27IntervalExtend L f (n : ZMod (16*L)) = f ⟨n,hn⟩ := by
  have hval : (n : ZMod (16*L)).val = n := ZMod.val_natCast_of_lt (by omega)
  simp [v27IntervalExtend, hval, hn]

/-- The degenerate cube yields unit modulus at every input point. -/
theorem v30_maximal_unit_modulus (L : ℕ) [NeZero (16*L)] (hL : 0 < L)
    (f : Fin L → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (hU : v27IntervalCubeRatio L f = 1)
    (i : Fin L) : ‖f i‖ = 1 := by
  let x : ZMod (16*L) := i.val
  let h : Fin 3 → ZMod (16*L) := fun _ => 0
  have hs : ∀ ω : Fin 3 → Fin 2, (v30Vertex L x h ω).val < L := by
    intro ω
    have hv : x.val = i.val := ZMod.val_natCast_of_lt (by have := i.isLt; omega)
    simpa [v30Vertex, h, hv] using i.isLt
  have he := v30_maximal_cube_terms L hL f hf hU x h hs
  have hu := v30_saturated_factor L f hf x h he (fun _ => 0)
  simpa [v30CubeFactor, v30Vertex, h, x, v30_interval_cast L f i.val i.isLt] using hu

/-- Explicit vertex value for an ordinary consecutive cube, with no wrap. -/
theorem v30_consecutive_vertex (L n : ℕ) (ω : Fin 3 → Fin 2) :
    v30Vertex L (n : ZMod (16*L)) (fun _ => 1) ω =
      ((n + ∑ i : Fin 3, (ω i).val : ℕ) : ZMod (16*L)) := by
  simp [v30Vertex, Nat.cast_add, Nat.cast_sum]

/-- The unit-step cube is the third multiplicative derivative. -/
theorem v30_consecutive_cube (L n : ℕ) (hn : n+3 < L) (f : Fin L → ℂ) :
    v30CubeTerm L f (n : ZMod (16*L)) (fun _ => 1) =
      f ⟨n, by omega⟩ * (star (f ⟨n+1, by omega⟩))^3 *
        (f ⟨n+2, by omega⟩)^3 * star (f ⟨n+3, hn⟩) := by
  classical
  have hu : (Finset.univ : Finset (Fin 3 → Fin 2)) =
      {![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
       ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]} := by decide
  unfold v30CubeTerm
  rw [hu]
  simp (disch := first | decide | omega) [Finset.prod_insert, v30CubeFactor, v30_consecutive_vertex,
    Fin.sum_univ_three, v30_interval_cast, hn] <;> ring

/-- Cancellation of unit-modulus factors converts the saturated cube to
an ordinary polynomial recurrence; no division by a possibly zero input. -/
theorem v30_cube_recurrence (a b c d : ℂ) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (h : a * (star b)^3 * c^3 * star d = 1) : d*b^3 = a*c^3 := by
  have hb' : b * star b = 1 := by rw [v28_star_self, hb]; norm_num
  have hd' : d * star d = 1 := by rw [v28_star_self, hd]; norm_num
  calc
    d*b^3 = (a*(star b)^3*c^3*star d)*(d*b^3) := by rw [h, one_mul]
    _ = a*c^3*(b*star b)^3*(d*star d) := by ring
    _ = a*c^3 := by rw [hb', hd']; simp

/-- Natural triangular exponents implement a quadratic polynomial orbit. -/
def v30Tri : ℕ → ℕ
  | 0 => 0
  | n+1 => v30Tri n + n

def v30QuadraticPhase (A B C : ℂ) (n : ℕ) : ℂ := A * B^n * C^(v30Tri n)

theorem v30_quadratic_norm (A B C : ℂ) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1)
    (hC : ‖C‖ = 1) (n : ℕ) : ‖v30QuadraticPhase A B C n‖ = 1 := by
  simp [v30QuadraticPhase, norm_mul, norm_pow, hA, hB, hC]

theorem v30_quadratic_recurrence (A B C : ℂ) (n : ℕ) :
    v30QuadraticPhase A B C (n+3) * (v30QuadraticPhase A B C (n+1))^3 =
      v30QuadraticPhase A B C n * (v30QuadraticPhase A B C (n+2))^3 := by
  simp [v30QuadraticPhase, v30Tri, pow_add, pow_succ] <;> ring

/-- Any two sequences obeying the recurrence and agreeing at 0,1,2
agree throughout the interval, provided their common factors are nonzero. -/
theorem v30_quadratic_uniqueness (L : ℕ) (f g : ℕ → ℂ)
    (hg : ∀ n, g n ≠ 0) (hbase : ∀ n, n < L → n < 3 → f n = g n)
    (hfrec : ∀ n, n+3 < L → f (n+3)*f (n+1)^3 = f n*f (n+2)^3)
    (hgrec : ∀ n, g (n+3)*g (n+1)^3 = g n*g (n+2)^3) :
    ∀ n, n < L → f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n < 3
    · exact hbase n hn hsmall
    · let m := n-3
      have hm : m+3 = n := by dsimp [m]; omega
      have h0 := ih m (by omega) (by omega)
      have h1 := ih (m+1) (by omega) (by omega)
      have h2 := ih (m+2) (by omega) (by omega)
      have hr := hfrec m (by omega)
      rw [h0,h1,h2, ← hgrec m, hm] at hr
      exact mul_right_cancel₀ (pow_ne_zero 3 (hg (m+1))) hr

/-- A genuine restricted inverse witness: normalized U³=1 and L≥3.
The phase is explicit, with three unit complex parameters; its degree-two
abelian orbit can subsequently be realized on a torus. General δ is open. -/
theorem v30_extremal_interval_quadratic (L : ℕ) [NeZero (16*L)] (hL : 3 ≤ L)
    (f : Fin L → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (hU : v27IntervalCubeRatio L f = 1) :
    ∃ A B C : ℂ, ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ ‖C‖ = 1 ∧
      ∀ i : Fin L, f i = v30QuadraticPhase A B C i.val := by
  let F (n : ℕ) : ℂ := if hn : n < L then f ⟨n,hn⟩ else 0
  have hF (n : ℕ) (hn : n < L) : ‖F n‖ = 1 := by
    simpa [F, hn] using v30_maximal_unit_modulus L (by omega) f hf hU ⟨n,hn⟩
  have hunit (n : ℕ) (hn : n < L) : F n * star (F n) = 1 := by
    rw [v28_star_self, hF n hn]; norm_num
  let A := F 0
  let B := F 1 * star (F 0)
  let C := F 2 * F 0 * (star (F 1))^2
  have hA : ‖A‖ = 1 := hF 0 (by omega)
  have hB : ‖B‖ = 1 := by simp [B, norm_mul, hF 0 (by omega), hF 1 (by omega)]
  have hC : ‖C‖ = 1 := by
    simp [C, norm_mul, norm_pow, hF 0 (by omega), hF 1 (by omega), hF 2 (by omega)]
  let g := v30QuadraticPhase A B C
  have hg (n : ℕ) : g n ≠ 0 := by
    have hh := v30_quadratic_norm A B C hA hB hC n
    change ‖g n‖ = 1 at hh
    exact fun hz => by simp [hz] at hh
  have hbase (n : ℕ) (hn : n < L) (hs : n < 3) : F n = g n := by
    have h0 := hunit 0 (by omega)
    have h1 := hunit 1 (by omega)
    interval_cases n
    · simp [g,v30QuadraticPhase,v30Tri,A]
    · dsimp [g,v30QuadraticPhase,v30Tri,A,B,C]
      calc
        F 1 = F 1*(F 0*star (F 0)) := by rw [h0,mul_one]
        _ = _ := by ring
    · dsimp [g,v30QuadraticPhase,v30Tri,A,B,C]
      calc
        F 2 = F 2*(F 0*star (F 0))^2*(F 1*star (F 1))^2 := by rw [h0,h1]; simp
        _ = _ := by ring
  have hrec (n : ℕ) (hn : n+3 < L) : F (n+3)*F (n+1)^3 = F n*F (n+2)^3 := by
    have hs : ∀ ω : Fin 3 → Fin 2,
        (v30Vertex L (n : ZMod (16*L)) (fun _ => 1) ω).val < L := by
      intro ω
      have h0 : (ω 0).val ≤ 1 := by have := (ω 0).isLt; omega
      have h1 : (ω 1).val ≤ 1 := by have := (ω 1).isLt; omega
      have h2 : (ω 2).val ≤ 1 := by have := (ω 2).isLt; omega
      have hk : n + ∑ i : Fin 3, (ω i).val < L := by rw [Fin.sum_univ_three]; omega
      rw [v30_consecutive_vertex, ZMod.val_natCast_of_lt (by omega)]
      exact hk
    have he := v30_maximal_cube_terms L (by omega) f hf hU _ _ hs
    rw [v30_consecutive_cube L n hn f] at he
    apply v30_cube_recurrence _ _ _ _ (hF (n+1) (by omega)) (hF (n+3) hn)
    simpa [F, show n < L by omega, show n+1 < L by omega, show n+2 < L by omega, hn] using he
  refine ⟨A,B,C,hA,hB,hC,?_⟩
  intro i
  have he := v30_quadratic_uniqueness L F g hg hbase hrec
    (v30_quadratic_recurrence A B C) i.val i.isLt
  simpa [F,i.isLt,g] using he

/-- The restricted inverse witness has correlation exactly one, not merely
an existence of a large derivative. -/
theorem v30_extremal_interval_correlation (L : ℕ) [NeZero (16*L)] (hL : 3 ≤ L)
    (f : Fin L → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) (hU : v27IntervalCubeRatio L f = 1) :
    ∃ A B C : ℂ, ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ ‖C‖ = 1 ∧
      (∑ i : Fin L, f i * star (v30QuadraticPhase A B C i.val)) = (L : ℂ) := by
  obtain ⟨A,B,C,hA,hB,hC,h⟩ := v30_extremal_interval_quadratic L hL f hf hU
  refine ⟨A,B,C,hA,hB,hC,?_⟩
  calc
    _ = ∑ _i : Fin L, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h i, v28_star_self, v30_quadratic_norm A B C hA hB hC]; norm_num
    _ = _ := by simp

end OpenAI086
