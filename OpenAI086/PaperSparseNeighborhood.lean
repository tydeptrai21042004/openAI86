import Mathlib
import OpenAI086.FiniteCommonNeighborEnergy
import OpenAI086.FiniteFourStepWalkEnergy

/-! Lemma 9.1, pp. 82–83: dependent random choice on a finite bipartite
adjacency matrix, pruning, and the four-step walk count. This is a
candidate for the dense-graph subargument, not the final sparse estimate. -/
namespace OpenAI086

noncomputable def v40Degree {U V : Type*} [Fintype U]
    (a : U → V → ℝ) (v : V) : ℝ := ∑ u, a u v

noncomputable def v40BadAt {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) (t : ℝ) (v : V) : ℝ := by
  classical
  exact ∑ u : U, ∑ w : U, if finiteCodegree a u w < t then a u v * a w v else 0

/-- The sum of bad-pair incidences over right vertices is bounded by the
codegree threshold times the number of ordered left pairs. -/
theorem v40_bad_mass {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ v, v40BadAt a t v) ≤ t*(Fintype.card U : ℝ)^2 := by
  classical
  unfold v40BadAt
  calc
    _ = ∑ u : U, ∑ w : U, ∑ v : V,
        if finiteCodegree a u w < t then a u v*a w v else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_comm]
    _ ≤ ∑ _u : U, ∑ _w : U, t := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro w _
      by_cases h : finiteCodegree a u w < t
      · simp only [if_pos h]
        change finiteCodegree a u w ≤ t
        exact h.le
      · simp [h, ht]
    _ = _ := by simp; ring

/-- A concrete neighborhood score, derived from the actual edge mass
and bad codegrees; no assumed existence of a good neighborhood. -/
theorem v40_neighborhood_score {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) (M η : ℝ) (hM : 0 < M) (hη : 0 < η)
    (ha : ∀ u v, 0 ≤ a u v)
    (hU : (Fintype.card U : ℝ) ≤ M)
    (hV : (Fintype.card V : ℝ) ≤ 2*M)
    (hedge : η*M^2 ≤ ∑ v, v40Degree a v) :
    ∃ v : V, η^2*M^2/8 ≤
      (v40Degree a v)^2 - 100*v40BadAt a (η^2*M/1600) v := by
  classical
  let t := η^2*M/1600
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let S : ℝ := ∑ v, (v40Degree a v)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs := finite_row_cauchy_schwarz (v40Degree a) (fun _ : V => (1:ℝ))
  have hcs' : (∑ v, v40Degree a v)^2 ≤ (Fintype.card V : ℝ)*S := by
    simpa [S, mul_comm] using hcs
  have he0 : 0 ≤ η*M^2 := by positivity
  have he2 : (η*M^2)^2 ≤ (∑ v, v40Degree a v)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hedge)
      (add_nonneg he0 (he0.trans hedge))]
  have hm : (η*M^2)^2 ≤ 2*M*S :=
    he2.trans (hcs'.trans (mul_le_mul_of_nonneg_right hV hS))
  have hS' : η^2*M^3/2 ≤ S := by
    apply (mul_le_mul_left hM).mp
    nlinarith only [hm]
  have hcard2 : (Fintype.card U : ℝ)^2 ≤ M^2 := by
    have hcard0 : 0 ≤ (Fintype.card U : ℝ) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hU) (add_nonneg hcard0 hM.le)]
  have hb := (v40_bad_mass a t ht).trans (mul_le_mul_of_nonneg_left hcard2 ht)
  have hscore : 7*η^2*M^3/16 ≤
      ∑ v, ((v40Degree a v)^2-100*v40BadAt a t v) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    change 7*η^2*M^3/16 ≤ S - 100*(∑ v, v40BadAt a t v)
    dsimp [t] at hb
    nlinarith only [hb, hS']
  by_contra! hn
  have hupper : (∑ v, ((v40Degree a v)^2-100*v40BadAt a t v)) ≤
      (Fintype.card V : ℝ)*(η^2*M^2/8) := by
    calc
      _ ≤ ∑ _v : V, η^2*M^2/8 := Finset.sum_le_sum (fun v _ => (hn v).le)
      _ = _ := by simp
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_right hV
    (show 0 ≤ η^2*M^2/8 by positivity))
  have hpos : 0 < η^2*M^3 := by positivity
  nlinarith only [hscore, hupper', hpos]

/-- Exact common-neighbor mass is symmetric and nonnegative. -/
theorem v40_codegree_properties {U V : Type*} [Fintype V]
    (a : U → V → ℝ) (ha : ∀ u v, 0 ≤ a u v) :
    (∀ u w, 0 ≤ finiteCodegree a u w) ∧
    (∀ u w, finiteCodegree a u w = finiteCodegree a w u) := by
  constructor
  · intro u w
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (ha u v) (ha w v))
  · intro u w
    unfold finiteCodegree
    exact Finset.sum_congr rfl (fun v _ => mul_comm _ _)

noncomputable def v40BadPartners {U : Type*} (Y : Finset U)
    (c : U → U → ℝ) (t : ℝ) (u : U) : ℝ := by
  classical
  exact ∑ w ∈ Y, if c u w < t then (1:ℝ) else 0

noncomputable def v40Pruned {U : Type*} (Y : Finset U)
    (c : U → U → ℝ) (t : ℝ) : Finset U := by
  classical
  exact Y.filter (fun u => v40BadPartners Y c t u ≤ (Y.card : ℝ)/4)

/-- Delete the heavy bad-partner rows. The conclusion is on the actual
filtered set of vertices, not an assumed cardinality of that set. -/
theorem v40_pruned_card {U : Type*} (Y : Finset U) (c : U → U → ℝ) (t : ℝ)
    (hY : 0 < Y.card)
    (hbad : (∑ u ∈ Y, v40BadPartners Y c t u) ≤ (Y.card : ℝ)^2/100) :
    (24:ℝ)/25*(Y.card : ℝ) ≤ ((v40Pruned Y c t).card : ℝ) := by
  classical
  let B := v40Pruned Y c t
  have hBY : B ⊆ Y := Finset.filter_subset _ _
  let R := Y \ B
  have hR : R ⊆ Y := Finset.sdiff_subset
  have hnonneg (u : U) : 0 ≤ v40BadPartners Y c t u := by
    unfold v40BadPartners
    exact Finset.sum_nonneg (fun w _ => by split_ifs <;> norm_num)
  have hr (u : U) (hu : u ∈ R) : (Y.card : ℝ)/4 ≤ v40BadPartners Y c t u := by
    have hmem := Finset.mem_sdiff.mp hu
    have hn : ¬ v40BadPartners Y c t u ≤ (Y.card : ℝ)/4 := by
      intro hh
      exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1, hh⟩)
    exact (lt_of_not_ge hn).le
  have hmass : (R.card : ℝ)*((Y.card : ℝ)/4) ≤ (Y.card : ℝ)^2/100 := by
    calc
      _ = ∑ _u ∈ R, (Y.card : ℝ)/4 := by simp
      _ ≤ ∑ u ∈ R, v40BadPartners Y c t u := Finset.sum_le_sum hr
      _ ≤ ∑ u ∈ Y, v40BadPartners Y c t u :=
        Finset.sum_le_sum_of_subset_of_nonneg hR (fun u _ _ => hnonneg u)
      _ ≤ _ := hbad
  have hy0 : 0 < (Y.card : ℝ) := by exact_mod_cast hY
  have hrsmall : (R.card : ℝ) ≤ (Y.card : ℝ)/25 := by
    apply (mul_le_mul_right hy0).mp
    nlinarith only [hmass]
  have hc : R.card + B.card = Y.card := by
    dsimp [R]
    rw [Finset.card_sdiff hBY]
    have hle := Finset.card_le_card hBY
    omega
  have hc' : (R.card : ℝ) + (B.card : ℝ) = (Y.card : ℝ) := by exact_mod_cast hc
  change (24:ℝ)/25*(Y.card : ℝ) ≤ (B.card : ℝ)
  linarith only [hc', hrsmall]

/-- Any two retained endpoints have many actual four-edge walks through
midpoints of Y. Repeated vertices are allowed, as in the manuscript. -/
theorem v40_pruned_walks {U : Type*} (Y : Finset U) (c : U → U → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (hc : ∀ u w, 0 ≤ c u w)
    (hsym : ∀ u w, c u w = c w u) (u w : U)
    (hu : u ∈ v40Pruned Y c t) (hw : w ∈ v40Pruned Y c t) :
    (Y.card : ℝ)/2*t^2 ≤ ∑ z ∈ Y, c u z*c z w := by
  classical
  have hu' := (Finset.mem_filter.mp hu).2
  have hw' := (Finset.mem_filter.mp hw).2
  have hpoint (z : U) :
      t^2*(1-(if c u z < t then (1:ℝ) else 0)-
        (if c w z < t then (1:ℝ) else 0)) ≤ c u z*c z w := by
    rw [hsym z w]
    split_ifs with h1 h2
    · nlinarith [sq_nonneg t, mul_nonneg (hc u z) (hc w z)]
    · norm_num <;> exact mul_nonneg (hc u z) (hc w z)
    · norm_num <;> exact mul_nonneg (hc u z) (hc w z)
    · simp only [sub_zero, mul_one]
      simpa [pow_two] using mul_le_mul (le_of_not_gt h1) (le_of_not_gt h2) ht (hc u z)
  have hsum := Finset.sum_le_sum (s := Y) (fun z _ => hpoint z)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  change t^2*((Y.card : ℝ)-v40BadPartners Y c t u-v40BadPartners Y c t w) ≤ _ at hsum
  have hmid : (Y.card : ℝ)/2 ≤
      (Y.card : ℝ)-v40BadPartners Y c t u-v40BadPartners Y c t w := by
    linarith only [hu', hw']
  calc
    _ ≤ ((Y.card : ℝ)-v40BadPartners Y c t u-v40BadPartners Y c t w)*t^2 :=
      mul_le_mul_of_nonneg_right hmid (sq_nonneg t)
    _ = t^2*((Y.card : ℝ)-v40BadPartners Y c t u-v40BadPartners Y c t w) := by ring
    _ ≤ _ := hsum

/-- Use the actual 0/1 adjacency matrix of a graph. -/
noncomputable def v40Adj {U V : Type*} (edge : U → V → Bool) (u : U) (v : V) : ℝ :=
  if edge u v then 1 else 0

/-- The degree and bad-pair mass of the matrix are exactly the
cardinality and bad-partner count on its true neighborhood. -/
theorem v40_actual_neighborhood {U V : Type*} [Fintype U] [Fintype V]
    (edge : U → V → Bool) (v : V) (t : ℝ) :
    let Y := Finset.univ.filter (fun u : U => edge u v = true)
    v40Degree (v40Adj edge) v = (Y.card : ℝ) ∧
    v40BadAt (v40Adj edge) t v =
      ∑ u ∈ Y, v40BadPartners Y (finiteCodegree (v40Adj edge)) t u := by
  classical
  dsimp only
  constructor
  · unfold v40Degree v40Adj
    calc
      _ = ∑ _u ∈ (Finset.univ.filter (fun u : U => edge u v = true)), (1:ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u _
        cases edge u v <;> simp
      _ = _ := by simp
  · unfold v40BadAt v40BadPartners
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : edge u v = true
    · have hAu : v40Adj edge u v = 1 := by simp [v40Adj, hu]
      simp only [hu, if_true, hAu, one_mul]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : edge w v = true <;>
        by_cases hc : finiteCodegree (v40Adj edge) u w < t <;> simp [hu, hw, hc, v40Adj]
    · simp [hu, v40Adj]

/-- Dense finite graph lemma with explicit constants. Produces an actual
set B and lower bounds four-step walk counts for all endpoints in B.
Proper coloring can subsequently encode the walks by their colors. -/
theorem v40_dense_graph_walks {U V : Type*} [Fintype U] [Fintype V]
    (edge : U → V → Bool) (M η : ℝ) (hM : 0 < M) (hη : 0 < η)
    (hU : (Fintype.card U : ℝ) ≤ M)
    (hV : (Fintype.card V : ℝ) ≤ 2*M)
    (hedge : η*M^2 ≤ ∑ v, v40Degree (v40Adj edge) v) :
    ∃ B : Finset U, η*M/5 ≤ (B.card : ℝ) ∧
      ∀ u ∈ B, ∀ w ∈ B,
        η^5*M^3/(8*1600^2) ≤
          ∑ z : U, finiteCodegree (v40Adj edge) u z * finiteCodegree (v40Adj edge) z w := by
  classical
  let a := v40Adj edge
  let c := finiteCodegree a
  let t := η^2*M/1600
  have ha (u : U) (v : V) : 0 ≤ a u v := by
    dsimp [a, v40Adj]; split_ifs <;> norm_num
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨v, hv⟩ := v40_neighborhood_score a M η hM hη ha hU hV hedge
  let Y := Finset.univ.filter (fun u : U => edge u v = true)
  obtain ⟨hd, hb⟩ := v40_actual_neighborhood edge v t
  change v40Degree a v = (Y.card : ℝ) at hd
  change v40BadAt a t v = ∑ u ∈ Y, v40BadPartners Y c t u at hb
  change η^2*M^2/8 ≤ (v40Degree a v)^2-100*v40BadAt a t v at hv
  rw [hd, hb] at hv
  have hbad0 : 0 ≤ ∑ u ∈ Y, v40BadPartners Y c t u := by
    apply Finset.sum_nonneg
    intro u _
    unfold v40BadPartners
    exact Finset.sum_nonneg (fun w _ => by split_ifs <;> norm_num)
  have hpos : 0 < η*M := mul_pos hη hM
  have hY : η*M/4 ≤ (Y.card : ℝ) := by
    by_contra! h
    have hs := mul_pos (sub_pos.mpr h) (show 0 < η*M/4+(Y.card : ℝ) by positivity)
    nlinarith only [hv, hbad0, hs, sq_nonneg (η*M)]
  have hY0 : 0 < Y.card := by
    have : 0 < (Y.card : ℝ) := (by positivity : 0 < η*M/4).trans_le hY
    exact_mod_cast this
  have hbad : (∑ u ∈ Y, v40BadPartners Y c t u) ≤ (Y.card : ℝ)^2/100 := by
    linarith [show 0 ≤ η^2*M^2/8 by positivity]
  let B := v40Pruned Y c t
  have hB := v40_pruned_card Y c t hY0 hbad
  refine ⟨B, ?_, ?_⟩
  · change η*M/5 ≤ ((v40Pruned Y c t).card : ℝ)
    linarith [hY, hB]
  · intro u hu w hw
    obtain ⟨hn, hs⟩ := v40_codegree_properties a ha
    have hwalk := v40_pruned_walks Y c t ht hn hs u w hu hw
    calc
      _ = η*M/8*t^2 := by dsimp [t]; ring
      _ ≤ (Y.card : ℝ)/2*t^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
        linarith
      _ ≤ ∑ z ∈ Y, c u z*c z w := hwalk
      _ ≤ ∑ z : U, c u z*c z w := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun z _ _ => mul_nonneg (hn u z) (hn z w))

end OpenAI086
