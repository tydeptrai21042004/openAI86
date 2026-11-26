/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license (LICENSE-REFERENCE-APACHE2).
Original authors: Claude. Extracted and namespaced for OpenAI086 V58.
Source: TrilinearHT/Auto/Sec14_2aShortBlockSampling.lean and Sec14_2bShortBlockSummation.lean.
-/
import Mathlib

namespace OpenAI086.AdaptedV58
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal BigOperators

/-! ### Leaf-depth rectangles (lem:shortblock, blueprint lines 2290-2296) -/

/-- The rectangles partitioning four-tuples of leaf depths in the proof of `lem:shortblock`:
`rep S v` (the minimum `v` is attained exactly on the slots `S`, at least two of them) and
`uniq a S h k` (the minimum is attained only at `a`; at scale `2^(h+1)` the depths of slot `a` and
of the slots `S` share the block `k`, with `a` in the lower and `S` in the upper half; all other
slots lie above that block). -/
inductive DepthRect
  | rep (S : Finset (Fin 4)) (v : ℕ)
  | uniq (a : Fin 4) (S : Finset (Fin 4)) (h k : ℕ)
  deriving DecidableEq

namespace DepthRect

/-- Admissible rectangle parameters. -/
def Valid : DepthRect → Prop
  | rep S _ => 2 ≤ S.card
  | uniq a S _ _ => a ∉ S ∧ S.Nonempty

/-- Membership of a depth tuple; it is a product of per-slot conditions. -/
def Mem : DepthRect → (Fin 4 → ℕ) → Prop
  | rep S v, d => ∀ j, (j ∈ S → d j = v) ∧ (j ∉ S → v < d j)
  | uniq a S h k, d => d a / 2 ^ h = 2 * k ∧
      ∀ j, j ≠ a → (j ∈ S → d j / 2 ^ h = 2 * k + 1) ∧ (j ∉ S → 2 * k + 2 ≤ d j / 2 ^ h)

/-- The separating depth `t`: all slots except possibly the heavy slot have depth at least `t`. -/
def sep : DepthRect → ℕ
  | rep _ v => v
  | uniq _ _ h k => (2 * k + 1) * 2 ^ h

theorem div_pow_succ (x h : ℕ) : x / 2 ^ (h + 1) = x / 2 ^ h / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- Agreement of the dyadic blocks persists at coarser scales. -/
theorem div_pow_eq_of_le {x y h h' : ℕ} (hh : h ≤ h') (e : x / 2 ^ h = y / 2 ^ h) :
    x / 2 ^ h' = y / 2 ^ h' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e]

/-- In a `uniq` rectangle the heavy slot is the strict minimum. -/
theorem uniq_lt {a : Fin 4} {S : Finset (Fin 4)} {h k : ℕ} {d : Fin 4 → ℕ}
    (hm : Mem (uniq a S h k) d) {j : Fin 4} (hj : j ≠ a) : d a < d j := by
  obtain ⟨ha, hS⟩ := hm
  have h1 : d a / 2 ^ h < d j / 2 ^ h := by
    by_cases hjS : j ∈ S
    · rw [ha, (hS j hj).1 hjS]; omega
    · have := (hS j hj).2 hjS; omega
  by_contra hle
  exact absurd (Nat.div_le_div_right (c := 2 ^ h) (not_lt.mp hle)) (not_le.mpr h1)

/-- Every tuple lies in a valid rectangle. -/
theorem exists_mem (d : Fin 4 → ℕ) : ∃ R, Valid R ∧ Mem R d := by
  classical
  obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  set v := d a
  set S0 := Finset.univ.filter fun j => d j = v
  by_cases hS0 : 2 ≤ S0.card
  · refine ⟨rep S0 v, hS0, fun j => ⟨fun hj => (Finset.mem_filter.mp hj).2, fun hj => ?_⟩⟩
    have : d j ≠ v := fun e => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩)
    exact lt_of_le_of_ne (ha j (Finset.mem_univ _)) (Ne.symm this)
  -- the minimum is unique
  have huniq : ∀ j, j ≠ a → v < d j := by
    intro j hj
    refine lt_of_le_of_ne (ha j (Finset.mem_univ _)) fun e => hS0 ?_
    have : ({a, j} : Finset (Fin 4)) ⊆ S0 := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.symm⟩
    exact (Finset.card_pair (Ne.symm hj)).symm.le.trans (Finset.card_le_card this)
  -- the second minimum
  have hne : (Finset.univ.erase a).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp)
  obtain ⟨i0, hi0, hmin2⟩ := Finset.exists_min_image (Finset.univ.erase a) d hne
  have hi0a : i0 ≠ a := (Finset.mem_erase.mp hi0).1
  set w := d i0
  have hvw : v < w := huniq i0 hi0a
  have hex : ∃ h, v / 2 ^ (h + 1) = w / 2 ^ (h + 1) :=
    ⟨w, by rw [Nat.div_eq_of_lt, Nat.div_eq_of_lt] <;>
      [exact (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega));
       exact hvw.trans ((Nat.lt_two_pow_self).trans
         (Nat.pow_lt_pow_right (by norm_num) (by omega)))]⟩
  set h := Nat.find hex
  have hh : v / 2 ^ (h + 1) = w / 2 ^ (h + 1) := Nat.find_spec hex
  have hh' : v / 2 ^ h ≠ w / 2 ^ h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0]; simp only [pow_zero, Nat.div_one]; omega
    · intro e
      have := Nat.find_min hex (show h - 1 < h by omega)
      rw [show h - 1 + 1 = h by omega] at this
      exact this e
  set k := v / 2 ^ (h + 1)
  have hv : v / 2 ^ h = 2 * k ∧ w / 2 ^ h = 2 * k + 1 := by
    have e1 : v / 2 ^ h / 2 = k := (div_pow_succ v h).symm
    have e2 : w / 2 ^ h / 2 = k := by rw [← div_pow_succ]; exact hh.symm
    have hle : v / 2 ^ h ≤ w / 2 ^ h := Nat.div_le_div_right hvw.le
    omega
  set S := (Finset.univ.erase a).filter fun j => d j / 2 ^ h = 2 * k + 1
  refine ⟨uniq a S h k, ⟨fun hm => (Finset.mem_erase.mp (Finset.mem_filter.mp hm).1).1 rfl,
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, hv.2⟩⟩⟩, hv.1, fun j hj => ⟨fun hjS =>
      (Finset.mem_filter.mp hjS).2, fun hjS => ?_⟩⟩
  have h1 : w ≤ d j := hmin2 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
  have h2 : 2 * k + 1 ≤ d j / 2 ^ h := hv.2 ▸ Nat.div_le_div_right h1
  have h3 : d j / 2 ^ h ≠ 2 * k + 1 := fun e =>
    hjS (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, e⟩)
  omega

/-- The rectangles partition the depth tuples: a tuple lies in exactly one valid rectangle. -/
theorem existsUnique_mem (d : Fin 4 → ℕ) : ∃! R, Valid R ∧ Mem R d := by
  classical
  obtain ⟨R, hR, hm⟩ := exists_mem d
  refine ⟨R, ⟨hR, hm⟩, ?_⟩
  -- canonical data of a valid rectangle containing `d`
  suffices key : ∀ R₁ R₂, Valid R₁ → Mem R₁ d → Valid R₂ → Mem R₂ d → R₁ = R₂ from
    fun R' ⟨hR', hm'⟩ => key R' R hR' hm' hR hm
  intro R₁ R₂ hv₁ hm₁ hv₂ hm₂
  -- a `rep` rectangle has two minimizing slots; a `uniq` rectangle has a strict minimum
  have rep_min : ∀ S v, Valid (rep S v) → Mem (rep S v) d → ∀ j, v ≤ d j ∧ (d j = v ↔ j ∈ S) := by
    intro S v _ hm j
    by_cases hj : j ∈ S
    · exact ⟨((hm j).1 hj).ge, ⟨fun _ => hj, fun _ => (hm j).1 hj⟩⟩
    · exact ⟨((hm j).2 hj).le, ⟨fun e => absurd e (ne_of_gt ((hm j).2 hj)), fun h => absurd h hj⟩⟩
  have rep_uniq : ∀ S v a S' h k, Valid (rep S v) → Mem (rep S v) d →
      Mem (uniq a S' h k) d → False := by
    intro S v a S' h k hv hm hm'
    obtain ⟨j1, hj1, j2, hj2, hj12⟩ :=
      Finset.one_lt_card.mp (show 1 < S.card by have : 2 ≤ S.card := hv; omega)
    have hva := (rep_min S v hv hm a).1
    have hj : ∃ j ∈ S, j ≠ a := by
      by_cases e : j1 = a
      · exact ⟨j2, hj2, fun e2 => hj12 (e.trans e2.symm)⟩
      · exact ⟨j1, hj1, e⟩
    obtain ⟨j, hjS, hja⟩ := hj
    have := uniq_lt hm' hja
    rw [(hm j).1 hjS] at this
    omega
  cases R₁ with
  | rep S v =>
    cases R₂ with
    | rep S' v' =>
      obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by have : 2 ≤ S.card := hv₁; omega)
      obtain ⟨j', hj'⟩ : S'.Nonempty := Finset.card_pos.mp (by have : 2 ≤ S'.card := hv₂; omega)
      have e1 := (hm₁ j).1 hj
      have e2 := (hm₂ j').1 hj'
      have hvv : v = v' := le_antisymm (e2 ▸ (rep_min S v hv₁ hm₁ j').1)
        (e1 ▸ (rep_min S' v' hv₂ hm₂ j).1)
      subst hvv
      have hSS : S = S' := by
        ext i
        rw [← (rep_min S v hv₁ hm₁ i).2, (rep_min S' v hv₂ hm₂ i).2]
      rw [hSS]
    | uniq a S' h k => exact (rep_uniq S v a S' h k hv₁ hm₁ hm₂).elim
  | uniq a S h k =>
    cases R₂ with
    | rep S' v' => exact (rep_uniq S' v' a S h k hv₂ hm₂ hm₁).elim
    | uniq a' S' h' k' =>
      have haa : a = a' := by
        by_contra hne
        have := uniq_lt hm₁ (Ne.symm hne)
        have := uniq_lt hm₂ hne
        omega
      subst haa
      -- the second minimum
      have hne : (Finset.univ.erase a).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp)
      obtain ⟨i0, hi0, hmin2⟩ := Finset.exists_min_image (Finset.univ.erase a) d hne
      have hi0a : i0 ≠ a := (Finset.mem_erase.mp hi0).1
      -- in each rectangle, `i0` lies in the upper half
      have upper : ∀ S h k, Valid (uniq a S h k) → Mem (uniq a S h k) d →
          d i0 / 2 ^ h = 2 * k + 1 := by
        intro S h k hv hm
        obtain ⟨j, hj⟩ := hv.2
        have hja : j ≠ a := fun e => hv.1 (e ▸ hj)
        have e1 := (hm.2 j hja).1 hj
        have hle : d i0 / 2 ^ h ≤ d j / 2 ^ h :=
          Nat.div_le_div_right (hmin2 j (Finset.mem_erase.mpr ⟨hja, Finset.mem_univ _⟩))
        have hge : 2 * k + 1 ≤ d i0 / 2 ^ h := by
          by_cases hi : i0 ∈ S
          · exact ((hm.2 i0 hi0a).1 hi).ge
          · have := (hm.2 i0 hi0a).2 hi; omega
        omega
      have u1 := upper S h k hv₁ hm₁
      have u2 := upper S' h' k' hv₂ hm₂
      have l1 := hm₁.1
      have l2 := hm₂.1
      -- the scale is the first level where the two depths share a block
      have blk : ∀ h k, d a / 2 ^ h = 2 * k → d i0 / 2 ^ h = 2 * k + 1 →
          d a / 2 ^ (h + 1) = d i0 / 2 ^ (h + 1) := by
        intro h k e1 e2
        rw [div_pow_succ, div_pow_succ, e1, e2]; omega
      have hhh : h = h' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := div_pow_eq_of_le (show h + 1 ≤ h' by omega) (blk h k l1 u1)
          rw [l2, u2] at this; omega
        · have := div_pow_eq_of_le (show h' + 1 ≤ h by omega) (blk h' k' l2 u2)
          rw [l1, u1] at this; omega
      subst hhh
      have hkk : k = k' := by omega
      subst hkk
      have hSS : S = S' := by
        ext j
        by_cases hja : j = a
        · subst hja; exact ⟨fun h => absurd h hv₁.1, fun h => absurd h hv₂.1⟩
        constructor
        · intro hj
          have e := (hm₁.2 j hja).1 hj
          by_contra hj'
          have := (hm₂.2 j hja).2 hj'; omega
        · intro hj
          have e := (hm₂.2 j hja).1 hj
          by_contra hj'
          have := (hm₁.2 j hja).2 hj'; omega
      rw [hSS]

/-- Positions at a level: for depths below `2^m`, a `uniq` rectangle has `h < m` and
`k < 2^(m-h-1)`; a `rep` rectangle has `v < 2^m`. -/
theorem uniq_bounds {a : Fin 4} {S : Finset (Fin 4)} {h k m : ℕ} {d : Fin 4 → ℕ}
    (hv : Valid (uniq a S h k)) (hm : Mem (uniq a S h k) d) (hd : ∀ j, d j < 2 ^ m) :
    h < m ∧ k < 2 ^ (m - h - 1) := by
  obtain ⟨j, hj⟩ := hv.2
  have hja : j ≠ a := fun e => hv.1 (e ▸ hj)
  have e := (hm.2 j hja).1 hj
  have hlt : d j / 2 ^ h < 2 ^ m / 2 ^ h :=
    Nat.div_lt_div_of_lt_of_dvd (Nat.pow_dvd_pow 2 (by
      by_contra hmh; push Not at hmh
      have : d j / 2 ^ h = 0 := Nat.div_eq_of_lt ((hd j).trans_le
        (Nat.pow_le_pow_right (by norm_num) hmh.le))
      omega)) (hd j)
  have hmh : h < m := by
    by_contra hmh; push Not at hmh
    have : d j / 2 ^ h = 0 := Nat.div_eq_of_lt ((hd j).trans_le
      (Nat.pow_le_pow_right (by norm_num) hmh))
    omega
  refine ⟨hmh, ?_⟩
  rw [Nat.pow_div hmh.le (by norm_num)] at hlt
  have : 2 ^ (m - h) = 2 * 2 ^ (m - h - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

end DepthRect

section WindowMass
variable {ι : Type*} (S : Finset ι) (aL lL : ι → ℝ)

/-! ### Window masses (lem:shortblock, blueprint lines 2328-2332) -/

/-- The leaf interval `[a_i, a_i + l_i)`. -/
def leafInterval (i : ι) : Set ℝ := Set.Ico (aL i) (aL i + lL i)

variable {S aL lL}

/-- The selected leaf union `E = ⋃_{i ∈ S} L_i`. -/
def leafUnion (S : Finset ι) (aL lL : ι → ℝ) : Set ℝ := ⋃ i ∈ S, leafInterval aL lL i

open Classical in
/-- The mass of `z` on the leaves meeting a set `W` is at most the total length of those leaves. -/
theorem leaf_mass_le (hdis : (S : Set ι).PairwiseDisjoint (leafInterval aL lL))
    (z : ℝ → ℂ) (hz : ∀ i ∈ S, ∫⁻ x in leafInterval aL lL i, ‖z x‖ₑ ^ 2 ≤ ENNReal.ofReal (lL i))
    (W : Set ℝ) :
    ∫⁻ x in W ∩ leafUnion S aL lL, ‖z x‖ₑ ^ 2 ≤
      volume (⋃ i ∈ S.filter fun i => (W ∩ leafInterval aL lL i).Nonempty,
        leafInterval aL lL i) := by
  classical
  set T := S.filter fun i => (W ∩ leafInterval aL lL i).Nonempty
  have hsub : W ∩ leafUnion S aL lL ⊆ ⋃ i ∈ T, leafInterval aL lL i := by
    rintro x ⟨hxW, hxE⟩
    simp only [leafUnion, Set.mem_iUnion] at hxE
    obtain ⟨i, hi, hx⟩ := hxE
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hi, x, hxW, hx⟩) hx
  have hdisT : (T : Set ι).PairwiseDisjoint (leafInterval aL lL) :=
    hdis.subset (by intro i hi; exact (Finset.mem_filter.mp hi).1)
  calc ∫⁻ x in W ∩ leafUnion S aL lL, ‖z x‖ₑ ^ 2
      ≤ ∫⁻ x in ⋃ i ∈ T, leafInterval aL lL i, ‖z x‖ₑ ^ 2 := lintegral_mono_set hsub
    _ = ∑ i ∈ T, ∫⁻ x in leafInterval aL lL i, ‖z x‖ₑ ^ 2 :=
        lintegral_biUnion_finset hdisT (fun _ _ => measurableSet_Ico) _
    _ ≤ ∑ i ∈ T, volume (leafInterval aL lL i) := by
        refine Finset.sum_le_sum fun i hi => (hz i (Finset.mem_filter.mp hi).1).trans ?_
        simp [leafInterval, Real.volume_Ico]
    _ = volume (⋃ i ∈ T, leafInterval aL lL i) :=
        (measure_biUnion_finset hdisT (fun _ _ => measurableSet_Ico)).symm

end WindowMass

section WindowMass
variable {ι : Type*} (S : Finset ι) (aL lL : ι → ℝ)
variable {S aL lL}

/-- Blueprint line 2331 (total mass): `∫_E |z|² ≤ |E|`. -/
theorem leafUnion_mass_le (hdis : (S : Set ι).PairwiseDisjoint (leafInterval aL lL))
    (z : ℝ → ℂ) (hz : ∀ i ∈ S, ∫⁻ x in leafInterval aL lL i, ‖z x‖ₑ ^ 2 ≤ ENNReal.ofReal (lL i)) :
    ∫⁻ x in leafUnion S aL lL, ‖z x‖ₑ ^ 2 ≤ volume (leafUnion S aL lL) := by
  have h := leaf_mass_le hdis z hz Set.univ
  rw [Set.univ_inter] at h
  refine h.trans (measure_mono ?_)
  intro x hx
  simp only [Set.mem_iUnion, Finset.mem_filter] at hx
  obtain ⟨i, ⟨hi, -⟩, hx⟩ := hx
  exact Set.mem_biUnion hi hx

/-- Blueprint lines 2332-2333 (regular slots): leaves of length at most `ρ` meeting an interval
window of length `ℓ` carry mass at most `ℓ + 2ρ`. -/
theorem leaf_window_mass_le (hdis : (S : Set ι).PairwiseDisjoint (leafInterval aL lL))
    (z : ℝ → ℂ) (hz : ∀ i ∈ S, ∫⁻ x in leafInterval aL lL i, ‖z x‖ₑ ^ 2 ≤ ENNReal.ofReal (lL i))
    {ρ : ℝ} (hρ : ∀ i ∈ S, lL i ≤ ρ) (x₀ ℓ : ℝ) :
    ∫⁻ x in Set.Ico x₀ (x₀ + ℓ) ∩ leafUnion S aL lL, ‖z x‖ₑ ^ 2 ≤ ENNReal.ofReal (ℓ + 2 * ρ) := by
  refine (leaf_mass_le hdis z hz _).trans ?_
  calc _ ≤ volume (Set.Ico (x₀ - ρ) (x₀ + ℓ + ρ)) := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_iUnion, Finset.mem_filter] at hx
        obtain ⟨i, ⟨hi, y, hyW, hyL⟩, hx⟩ := hx
        simp only [leafInterval, Set.mem_Ico] at hyW hyL hx ⊢
        have := hρ i hi
        constructor <;> linarith
    _ = _ := by rw [Real.volume_Ico]; congr 1; ring

/-- Blueprint line 2334 (local bound): if every leaf meeting a set `I` lies inside `I`, the mass
on `I` is at most `|I|`. -/
theorem leaf_local_mass_le (hdis : (S : Set ι).PairwiseDisjoint (leafInterval aL lL))
    (z : ℝ → ℂ) (hz : ∀ i ∈ S, ∫⁻ x in leafInterval aL lL i, ‖z x‖ₑ ^ 2 ≤ ENNReal.ofReal (lL i))
    (I : Set ℝ) (hI : ∀ i ∈ S, (I ∩ leafInterval aL lL i).Nonempty → leafInterval aL lL i ⊆ I) :
    ∫⁻ x in I ∩ leafUnion S aL lL, ‖z x‖ₑ ^ 2 ≤ volume I := by
  refine (leaf_mass_le hdis z hz I).trans (measure_mono ?_)
  intro x hx
  simp only [Set.mem_iUnion, Finset.mem_filter] at hx
  obtain ⟨i, ⟨hi, hne⟩, hx⟩ := hx
  exact hI i hi hne hx

end WindowMass

/-- The `δ`-windows `[δ(n + c), δ(n + c + 1))`, `n ∈ ℤ`, tile the line: for every shift `c`,
`Σ_n ∫_{window n} g = ∫ g`. -/
theorem lintegral_window_tiling {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (g : ℝ → ℝ≥0∞) :
    ∑' n : ℤ, ∫⁻ x in Set.Ico (δ * (n + c)) (δ * (n + c + 1)), g x = ∫⁻ x, g x := by
  have hdis : Pairwise (Function.onFun Disjoint
      fun n : ℤ => Set.Ico (δ * (n + c)) (δ * (n + c + 1))) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hx hx' => hnm ?_
    simp only [Set.mem_Ico] at hx hx'
    have h1 : (n : ℝ) < m + 1 := by nlinarith
    have h2 : (m : ℝ) < n + 1 := by nlinarith
    have h1' : n < m + 1 := by exact_mod_cast h1
    have h2' : m < n + 1 := by exact_mod_cast h2
    omega
  have hcov : (⋃ n : ℤ, Set.Ico (δ * (n + c)) (δ * (n + c + 1))) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_Ico]
    refine ⟨⌊x / δ - c⌋, ?_, ?_⟩
    · have := Int.floor_le (x / δ - c)
      have h : δ * (⌊x / δ - c⌋ + c) ≤ δ * (x / δ) := by
        apply mul_le_mul_of_nonneg_left (by linarith only [this]) hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at h
    · have := Int.lt_floor_add_one (x / δ - c)
      have h : δ * (x / δ) < δ * (⌊x / δ - c⌋ + c + 1) := by
        apply mul_lt_mul_of_pos_left (by linarith only [this]) hδ
      rwa [mul_div_cancel₀ _ hδ.ne'] at h
  rw [← lintegral_iUnion (fun _ => measurableSet_Ico) hdis, hcov, Measure.restrict_univ]

/-- Windows of `K` consecutive unit lengths cover every point `K` times:
`Σ_n ∫_{[δ(n+c), δ(n+c+K))} g = K ∫ g` (the lift intervals in slots `2, 3`). -/
theorem lintegral_window_sum (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (g : ℝ → ℝ≥0∞) :
    ∑' n : ℤ, ∫⁻ x in Set.Ico (δ * (n + c)) (δ * (n + c + K)), g x = K * ∫⁻ x, g x := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hsplit : ∀ n : ℤ, ∫⁻ x in Set.Ico (δ * (n + c)) (δ * (n + c + (K + 1 : ℕ))), g x =
        (∫⁻ x in Set.Ico (δ * (n + c)) (δ * (n + c + K)), g x) +
          ∫⁻ x in Set.Ico (δ * (n + (c + K))) (δ * (n + (c + K) + 1)), g x := by
      intro n
      rw [← lintegral_union measurableSet_Ico]
      · congr 2
        rw [show δ * ((n : ℝ) + (c + K)) = δ * (n + c + K) by ring,
          show δ * ((n : ℝ) + (c + K) + 1) = δ * (n + c + ((K + 1 : ℕ) : ℝ)) by push_cast; ring,
          Set.Ico_union_Ico_eq_Ico]
        · apply mul_le_mul_of_nonneg_left _ hδ.le
          have := (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
          linarith
        · apply mul_le_mul_of_nonneg_left _ hδ.le
          push_cast; linarith
      · rw [show δ * (n + (c + K)) = δ * (n + c + K) by ring]
        exact Set.Ico_disjoint_Ico_same
    simp_rw [hsplit]
    rw [ENNReal.tsum_add, ih, lintegral_window_tiling hδ]
    push_cast; ring

/-! V59 additions: designated mask separation and exact partition of unity.
Adapted from the same attributed reference Sec14_2a and Sec14_2b. -/
namespace DepthRect
/-- The heavy slot `a` of a rectangle (for `rep`, the least attaining slot). -/
noncomputable def heavy : DepthRect → Fin 4
  | rep S _ => if h : S.Nonempty then S.min' h else 0
  | uniq a _ _ _ => a

/-- The designated slot `b` of a rectangle (blueprint line 2292). -/
noncomputable def desig : DepthRect → Fin 4
  | rep S _ => if h : (S.erase (if h : S.Nonempty then S.min' h else 0)).Nonempty then
      (S.erase (if h : S.Nonempty then S.min' h else 0)).min' h else 0
  | uniq _ S _ _ => if h : S.Nonempty then S.min' h else 0

theorem heavy_mem_rep {S : Finset (Fin 4)} {v : ℕ} (hv : Valid (rep S v)) :
    heavy (rep S v) ∈ S := by
  have hS : S.Nonempty := Finset.card_pos.mp (by have : 2 ≤ S.card := hv; omega)
  simp only [heavy, hS, ↓reduceDIte]
  exact Finset.min'_mem S hS

theorem desig_mem_rep {S : Finset (Fin 4)} {v : ℕ} (hv : Valid (rep S v)) :
    desig (rep S v) ∈ S ∧ desig (rep S v) ≠ heavy (rep S v) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by have : 2 ≤ S.card := hv; omega)
  have hE : (S.erase (S.min' hS)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.min'_mem S hS)]
    have : 2 ≤ S.card := hv; omega
  simp only [desig, heavy, hS, ↓reduceDIte, hE]
  have := Finset.min'_mem _ hE
  exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩

theorem desig_mem_uniq {a : Fin 4} {S : Finset (Fin 4)} {h k : ℕ} (hv : Valid (uniq a S h k)) :
    desig (uniq a S h k) ∈ S ∧ desig (uniq a S h k) ≠ heavy (uniq a S h k) := by
  obtain ⟨haS, hS⟩ := hv
  simp only [desig, heavy, hS, ↓reduceDIte]
  have := Finset.min'_mem S hS
  exact ⟨this, fun e => haS (e ▸ this)⟩

theorem desig_ne_heavy {R : DepthRect} (hv : Valid R) : desig R ≠ heavy R := by
  cases R with
  | rep S v => exact (desig_mem_rep hv).2
  | uniq a S h k => exact (desig_mem_uniq hv).2

/-- The level of a rectangle: its slot assignment and scale, forgetting the position. -/
def level : DepthRect → DepthRect
  | rep S _ => rep S 0
  | uniq a S h _ => uniq a S h 0

/-- The per-slot condition of a rectangle; membership is the product of these conditions. -/
def Side : DepthRect → Fin 4 → ℕ → Prop
  | rep S v, j, x => (j ∈ S → x = v) ∧ (j ∉ S → v < x)
  | uniq a S h k, j, x => if j = a then x / 2 ^ h = 2 * k else
      (j ∈ S → x / 2 ^ h = 2 * k + 1) ∧ (j ∉ S → 2 * k + 2 ≤ x / 2 ^ h)

instance (R : DepthRect) (j : Fin 4) (x : ℕ) : Decidable (Side R j x) := by
  cases R <;> unfold Side <;> infer_instance

instance : DecidablePred Valid := fun R => by
  cases R <;> unfold Valid <;> infer_instance

theorem mem_iff_side (R : DepthRect) (d : Fin 4 → ℕ) : Mem R d ↔ ∀ j, Side R j (d j) := by
  cases R with
  | rep S v => rfl
  | uniq a S h k =>
    simp only [Mem, Side]
    constructor
    · rintro ⟨ha, hS⟩ j
      by_cases hj : j = a
      · subst hj; simp [ha]
      · simp only [hj, ↓reduceIte]; exact hS j hj
    · intro h
      refine ⟨by simpa using h a, fun j hj => ?_⟩
      have := h j
      simpa [hj] using this

/-- The finitely many rectangle parameters relevant for depths below `2^m`. -/
noncomputable def upTo (m : ℕ) : Finset DepthRect :=
  ((Finset.univ : Finset (Finset (Fin 4))) ×ˢ Finset.range (2 ^ m)).image
      (fun p => rep p.1 p.2) ∪
    ((Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Finset (Fin 4))) ×ˢ
      Finset.range m ×ˢ Finset.range (2 ^ m)).image (fun p => uniq p.1 p.2.1 p.2.2.1 p.2.2.2)

theorem mem_upTo_of_mem {m : ℕ} {R : DepthRect} {d : Fin 4 → ℕ} (hd : ∀ j, d j < 2 ^ m)
    (hv : Valid R) (hm : Mem R d) : R ∈ upTo m := by
  unfold upTo
  rw [Finset.mem_union]
  cases R with
  | rep S v =>
    left
    obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by have : 2 ≤ S.card := hv; omega)
    refine Finset.mem_image.mpr ⟨(S, v), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
    rw [← (hm j).1 hj]; exact hd j
  | uniq a S h k =>
    right
    obtain ⟨hhm, hk⟩ := uniq_bounds hv hm hd
    refine Finset.mem_image.mpr ⟨(a, S, h, k), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
    refine ⟨hhm, hk.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- Blueprint lines 2290-2296 (the rectangles partition the depth tuples), as a partition of
unity: for depths below `2^m`, exactly one valid rectangle of `upTo m` has all four side
conditions. -/
theorem side_partition (m : ℕ) (d : Fin 4 → ℕ) (hd : ∀ j, d j < 2 ^ m) :
    ∑ R ∈ (upTo m).filter Valid, ∏ j, (if Side R j (d j) then (1 : ℂ) else 0) = 1 := by
  classical
  obtain ⟨R, ⟨hv, hm⟩, huniq⟩ := existsUnique_mem d
  rw [Finset.sum_eq_single R]
  · rw [Finset.prod_eq_one fun j _ => ite_eq_left ((mem_iff_side R d).mp hm j)]
  · intro R' hR' hne
    have hv' := (Finset.mem_filter.mp hR').2
    have : ¬ Mem R' d := fun hm' => hne (huniq R' ⟨hv', hm'⟩)
    rw [mem_iff_side] at this
    push Not at this
    obtain ⟨j, hj⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  · intro hR
    exact absurd (Finset.mem_filter.mpr ⟨mem_upTo_of_mem hd hv hm, hv⟩) hR

/-- The heavy slot has depth at most the separating depth. -/
theorem side_heavy_le {R : DepthRect} (hv : Valid R) {x : ℕ} (hx : Side R (heavy R) x) :
    x ≤ sep R := by
  cases R with
  | rep S v =>
    have := (hx.1 (heavy_mem_rep hv))
    simp only [sep]; omega
  | uniq a S h k =>
    simp only [Side, heavy, ↓reduceIte] at hx
    simp only [sep]
    have h2 : 0 < 2 ^ h := by positivity
    have hlt : x < 2 ^ h * (x / 2 ^ h + 1) := Nat.lt_mul_div_succ x h2
    rw [hx] at hlt
    nlinarith

/-- All other slots have depth at least the separating depth. -/
theorem sep_le_side {R : DepthRect} {j : Fin 4} (hj : j ≠ heavy R) {x : ℕ} (hx : Side R j x) :
    sep R ≤ x := by
  cases R with
  | rep S v =>
    simp only [sep]
    by_cases hjS : j ∈ S
    · exact (hx.1 hjS).ge
    · exact (hx.2 hjS).le
  | uniq a S h k =>
    simp only [heavy] at hj
    simp only [Side, hj, ↓reduceIte] at hx
    simp only [sep]
    have hq : 2 * k + 1 ≤ x / 2 ^ h := by
      by_cases hjS : j ∈ S
      · exact (hx.1 hjS).ge
      · have := hx.2 hjS; omega
    calc (2 * k + 1) * 2 ^ h ≤ x / 2 ^ h * 2 ^ h := Nat.mul_le_mul_right _ hq
      _ ≤ x := Nat.div_mul_le_self x _

/-- Within a level, the heavy masks of distinct positions are disjoint. -/
theorem heavy_disjoint {R R' : DepthRect} (hv : Valid R) (hl : level R = level R')
    (hne : R ≠ R') {x : ℕ} (h1 : Side R (heavy R) x) (h2 : Side R' (heavy R') x) : False := by
  cases R with
  | rep S v =>
    cases R' with
    | rep S' v' =>
      simp only [level, rep.injEq, and_true] at hl
      subst hl
      have hv' : Valid (rep S v') := hv
      have e1 := h1.1 (heavy_mem_rep hv)
      have e2 := h2.1 (heavy_mem_rep hv')
      exact hne (by rw [← e1, ← e2])
    | uniq => simp [level] at hl
  | uniq a S h k =>
    cases R' with
    | rep => simp [level] at hl
    | uniq a' S' h' k' =>
      simp only [level, uniq.injEq, and_true] at hl
      obtain ⟨rfl, rfl, rfl⟩ := hl
      simp only [Side, heavy, ↓reduceIte] at h1 h2
      exact hne (by congr 1; omega)

/-- Within a level, the designated masks of distinct positions are disjoint. -/
theorem desig_disjoint {R R' : DepthRect} (hv : Valid R) (hl : level R = level R')
    (hne : R ≠ R') {x : ℕ} (h1 : Side R (desig R) x) (h2 : Side R' (desig R') x) : False := by
  cases R with
  | rep S v =>
    cases R' with
    | rep S' v' =>
      simp only [level, rep.injEq, and_true] at hl
      subst hl
      have hv' : Valid (rep S v') := hv
      have e1 := h1.1 (desig_mem_rep hv).1
      have e2 := h2.1 (by
        have := (desig_mem_rep hv').1; simpa [desig] using this)
      exact hne (by rw [← e1, ← e2])
    | uniq => simp [level] at hl
  | uniq a S h k =>
    cases R' with
    | rep => simp [level] at hl
    | uniq a' S' h' k' =>
      simp only [level, uniq.injEq, and_true] at hl
      obtain ⟨rfl, rfl, rfl⟩ := hl
      have hd := desig_mem_uniq hv
      simp only [Side, (show desig (uniq a S h k) ≠ a from hd.2), ↓reduceIte] at h1
      have hd' : desig (uniq a S h k') = desig (uniq a S h k) := rfl
      rw [hd'] at h2
      simp only [Side, (show desig (uniq a S h k) ≠ a from hd.2), ↓reduceIte] at h2
      have := h1.1 hd.1
      have := h2.1 hd.1
      exact hne (by congr 1; omega)


end DepthRect

end OpenAI086.AdaptedV58
#print axioms OpenAI086.AdaptedV58.DepthRect.existsUnique_mem
#print axioms OpenAI086.AdaptedV58.DepthRect.uniq_bounds
#print axioms OpenAI086.AdaptedV58.leaf_mass_le
#print axioms OpenAI086.AdaptedV58.leaf_window_mass_le
#print axioms OpenAI086.AdaptedV58.leaf_local_mass_le
#print axioms OpenAI086.AdaptedV58.lintegral_window_tiling
#print axioms OpenAI086.AdaptedV58.lintegral_window_sum

#print axioms OpenAI086.AdaptedV58.DepthRect.side_partition
#print axioms OpenAI086.AdaptedV58.DepthRect.side_heavy_le
#print axioms OpenAI086.AdaptedV58.DepthRect.sep_le_side
#print axioms OpenAI086.AdaptedV58.DepthRect.heavy_disjoint
#print axioms OpenAI086.AdaptedV58.DepthRect.desig_disjoint
