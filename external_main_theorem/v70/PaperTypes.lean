/-
Adapted from TrilinearHT/Auto/Sec13_5RepresentativesComponentSizesFirstTops.lean
Copyright (c) 2026 Joris Roos. Authors: Claude.
Released under Apache 2.0; see LICENSE-REFERENCE-APACHE2.
V70 changes the type rank to the manuscript's floor-log base 11/10,
and introduces the manuscript's stronger goodness predicate.
-/
import TrilinearHT.Auto.Sec15_4VerificationCountingHypotheses
import SourceV56EntryRank

namespace OpenAI086.ReferenceV70
open Auto OpenAI086.AdaptedV56
open scoped BigOperators

/-- Equal printed logarithmic types of positive sizes imply the strict
size comparison used in Sections 8.5 and 8.8. -/
theorem floorlog_ratio {a b : ℕ} (ha : 0 < a)
    (he : v57FloorLog a = v57FloorLog b) : 10*b < 11*a := by
  by_contra hn
  have hr : 11*a ≤ 10*b := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hb : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hrR : (11 : ℝ)*a ≤ 10*b := by exact_mod_cast hr
  have hmul : (11/10 : ℝ)*(a : ℝ) ≤ b := by linarith
  have hbase : 0 < Real.log (11/10 : ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 11/10) haR) hmul
  rw [Real.log_mul (by norm_num : (11/10 : ℝ) ≠ 0) haR.ne'] at hlog
  have hstep : Real.log (a : ℝ) / Real.log (11/10 : ℝ) + 1 ≤
      Real.log (b : ℝ) / Real.log (11/10 : ℝ) := by
    apply (le_div_iff₀ hbase).mpr
    rw [add_mul, div_mul_cancel₀ _ hbase.ne', one_mul]
    linarith
  have hlo : (v57FloorLog a : ℝ) ≤ Real.log (a : ℝ) / Real.log (11/10 : ℝ) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg ha1) hbase.le)
  have hhi : Real.log (b : ℝ) / Real.log (11/10 : ℝ) < (v57FloorLog b : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [← he] at hhi
  linarith

theorem card_lt_two_mul_of_floorlog_eq {a b : ℕ} (ha : 0 < a)
    (he : v57FloorLog a = v57FloorLog b) : b < 2*a := by
  have := floorlog_ratio ha he
  omega

end OpenAI086.ReferenceV70

namespace Auto.ModeComponents
open OpenAI086.AdaptedV56 OpenAI086.ReferenceV70
variable {Mode P : Type*} [DecidableEq Mode] [DecidableEq P]

/-- Exact cardinality and good-primary tests of paper Section 8.5.
This is not defined as the weaker reference nine-tenths test. -/
def PaperGood (C : ModeComponents Mode P) (Δ : ℕ) (goodP : ℕ → P → Prop)
    [∀ h, DecidablePred (goodP h)] (h : ℕ) (m : Mode) : Prop :=
  Δ ≤ h ∧ v57FloorLog (C.labels (C.E (h-Δ) m)).card =
    v57FloorLog (C.labels (C.F h m)).card ∧
    9 * (C.labels (C.F h m)).card ≤ 10 * ((C.labels (C.F h m)).filter (goodP h)).card

/-- Only this direction is valid: a paper-good mode meets the reference test. -/
theorem paperGood_to_good (C : ModeComponents Mode P) (Δ : ℕ) (goodP : ℕ → P → Prop)
    [∀ h, DecidablePred (goodP h)] {h : ℕ} {m : Mode}
    (hm : C.PaperGood Δ goodP h m) : C.Good Δ goodP h m := by
  obtain ⟨hd, he, hg⟩ := hm
  have hp : 0 < (C.labels (C.E (h-Δ) m)).card :=
    Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (C.E_self _ _)⟩
  have hrat := floorlog_ratio hp he
  refine ⟨hd, ?_, hg⟩
  omega

/-- First assertion of Lemma 8.4 for the printed predicate. -/
theorem paper_good_same_predecessor (C : ModeComponents Mode P) (Δ : ℕ)
    (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)]
    (hstab : ∀ h x x', goodP h (C.π x) → C.π x' = C.π x → x' ∈ C.F h x → x' ∈ C.E (h - Δ) x)
    {h : ℕ} {m m' : Mode} (hm : C.PaperGood Δ goodP h m)
    (hm' : C.PaperGood Δ goodP h m') (hmem : m' ∈ C.F h m) :
    C.E (h-Δ) m = C.E (h-Δ) m' :=
  C.good_same_predecessor Δ goodP hstab (C.paperGood_to_good Δ goodP hm)
    (C.paperGood_to_good Δ goodP hm') hmem

/-- The printed good predicates are constant on minimal PRE components. -/
theorem paper_good_minimal_pre (C : ModeComponents Mode P) (Δ : ℕ)
    (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)]
    {m m' : Mode} (hmem : m' ∈ C.E 0 m) (h : ℕ) :
    C.PaperGood Δ goodP h m ↔ C.PaperGood Δ goodP h m' := by
  have hE := C.E_eq_of_mem (C.E_mono 0 (h-Δ) m (Nat.zero_le _) hmem)
  have hF := (C.F_comp h m m' (C.F_mono 0 h m (Nat.zero_le _) (C.E_le_F 0 m hmem))).symm
  unfold PaperGood
  rw [hE, hF]


open Classical in
noncomputable def paperBadHeights (C : ModeComponents Mode P) (Δ : ℕ)
    (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)] (J : ℕ) (m : Mode) : Finset ℕ :=
  (Finset.range (J+1)).filter fun h => ¬ C.PaperGood Δ goodP h m

def PaperCore (C : ModeComponents Mode P) (Δ : ℕ)
    (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)] (J : ℕ) (δ : ℝ) (m : Mode) : Prop :=
  ((C.paperBadHeights Δ goodP J m).card : ℝ) ≤ δ*(J+1)

theorem paper_core_minimal_pre (C : ModeComponents Mode P) (Δ : ℕ)
    (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)] (J : ℕ) (δ : ℝ)
    {m m' : Mode} (hm : m' ∈ C.E 0 m) :
    C.PaperCore Δ goodP J δ m ↔ C.PaperCore Δ goodP J δ m' := by
  classical
  have he : C.paperBadHeights Δ goodP J m = C.paperBadHeights Δ goodP J m' := by
    unfold paperBadHeights
    exact Finset.filter_congr fun h _ => by rw [C.paper_good_minimal_pre Δ goodP hm h]
  unfold PaperCore
  rw [he]

variable (C : ModeComponents Mode P)

theorem paper_core_bad_proportion (Δ : ℕ) (goodP : ℕ → P → Prop) [∀ h, DecidablePred (goodP h)]
    {J : ℕ} (hJ : 2 ≤ J) {δ : ℝ} (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) {m : Mode}
    (hm : C.PaperCore Δ goodP J δ m) :
    ((C.paperBadHeights Δ goodP J m ∩ upperHeights J δ).card : ℝ) ≤
      2 * δ * (upperHeights J δ).card := by
  classical
  set c := ⌈4 * δ * J⌉₊
  have hup : upperHeights J δ = Finset.Ico c (J + 1) := by
    ext h
    simp only [upperHeights, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor <;> intro hh <;> omega
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hc : (c : ℝ) < 4 * δ * J + 1 := Nat.ceil_lt_add_one (by positivity)
  have hcJ : c ≤ J + 1 := by
    have : (c : ℝ) ≤ J + 1 := by nlinarith
    exact_mod_cast this
  have hcard : ((upperHeights J δ).card : ℝ) = J + 1 - c := by
    rw [hup, Nat.card_Ico, Nat.cast_sub hcJ]; push_cast; ring
  have h1 : ((C.paperBadHeights Δ goodP J m).card : ℝ) ≤ δ * (J + 1) := hm
  have h2 : ((C.paperBadHeights Δ goodP J m ∩ upperHeights J δ).card : ℝ) ≤
      (C.paperBadHeights Δ goodP J m).card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hkey : 2 * (c : ℝ) ≤ J + 1 := by nlinarith
  rw [hcard]
  nlinarith only [mul_le_mul_of_nonneg_left hkey hδ.le, h1, h2]


/-- Two paper-core modes in the same minimal CURRENT component admit an
actual common good height below the upper range. This proves the remaining
coherence assertion of Lemma 8.4 on the reference component data. -/
theorem paper_core_current_coherence (Δ : ℕ) (goodP : ℕ → P → Prop)
    [∀ h, DecidablePred (goodP h)] {J : ℕ} (hJ : 2 ≤ J)
    {δ : ℝ} (hδ : 0 < δ) (hδ16 : δ ≤ 1/16)
    (hstab : ∀ h x x', goodP h (C.π x) → C.π x' = C.π x →
      x' ∈ C.F h x → x' ∈ C.E (h-Δ) x)
    {m m' : Mode} (hm : C.PaperCore Δ goodP J δ m)
    (hm' : C.PaperCore Δ goodP J δ m') (hF0 : m' ∈ C.F 0 m) :
    ∀ h ∈ upperHeights J δ,
      C.E (h-Δ) m = C.E (h-Δ) m' ∧
      (C.PaperGood Δ goodP h m ↔ C.PaperGood Δ goodP h m') := by
  classical
  let c : ℕ := ⌈4 * δ * J⌉₊
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hcLower : 4*δ*J ≤ (c : ℝ) := Nat.le_ceil _
  have hcUpper : (c : ℝ) < 4*δ*J+1 := Nat.ceil_lt_add_one (by positivity)
  have hcJ : c ≤ J+1 := by
    have hr : (c : ℝ) ≤ (J : ℝ)+1 := by nlinarith
    exact_mod_cast hr
  have hstrict : 2*δ*((J:ℝ)+1) < (c:ℝ) := by
    nlinarith [mul_pos hδ (show 0 < (J:ℝ)-1 by linarith)]
  have hExists : ∃ h₀ < c, C.PaperGood Δ goodP h₀ m ∧ C.PaperGood Δ goodP h₀ m' := by
    by_contra hn
    have hcover : Finset.range c ⊆ C.paperBadHeights Δ goodP J m ∪ C.paperBadHeights Δ goodP J m' := by
      intro k hk
      have hkC := Finset.mem_range.mp hk
      have hkJ : k < J+1 := lt_of_lt_of_le hkC hcJ
      by_cases hg : C.PaperGood Δ goodP k m
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkJ, fun hg' => hn ⟨k,hkC,hg,hg'⟩⟩
      · apply Finset.mem_union.mpr
        left
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkJ,hg⟩
    have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    rw [Finset.card_range] at hcard
    have hcardR : (c:ℝ) ≤ (C.paperBadHeights Δ goodP J m).card +
        ((C.paperBadHeights Δ goodP J m').card : ℝ) := by exact_mod_cast hcard
    change ((C.paperBadHeights Δ goodP J m).card : ℝ) ≤ δ*((J:ℝ)+1) at hm
    change ((C.paperBadHeights Δ goodP J m').card : ℝ) ≤ δ*((J:ℝ)+1) at hm'
    linarith
  obtain ⟨h₀,h₀c,hg,hg'⟩ := hExists
  have hF₀ := C.F_mono 0 h₀ m (Nat.zero_le _) hF0
  have hE₀ := C.paper_good_same_predecessor Δ goodP hstab hg hg' hF₀
  intro h hh
  have hch : c ≤ h := (Finset.mem_filter.mp hh).2
  have hh₀ : h₀-Δ ≤ h-Δ := Nat.sub_le_sub_right (le_trans h₀c.le hch) _
  have hmem : m' ∈ C.E (h₀-Δ) m := by rw [hE₀]; exact C.E_self _ _
  have he : C.E (h-Δ) m = C.E (h-Δ) m' := C.E_eq_of_mem (C.E_mono _ _ m hh₀ hmem)
  have hf : C.F h m = C.F h m' := (C.F_comp h m m' (C.F_mono 0 h m (Nat.zero_le _) hF0)).symm
  refine ⟨he,?_⟩
  unfold PaperGood
  rw [he,hf]

end Auto.ModeComponents

namespace Auto.ModeSystem
open OpenAI086.AdaptedV56 OpenAI086.ReferenceV70
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

open Classical in
/-- Blueprint lines 2172-2191 (`THT.Modes.hereditaryRepresentatives`) for all successful
components at once: the nodes are triples `(b, J, m)` with one good mode `m` per CURRENT component
at each pre-cell. The chronological representatives lie in their predecessors, are inherited under
predecessor inclusion, and different representatives on comparable nodes have disjoint
predecessors in different later CURRENT components. -/
theorem attempt_representatives_paper (Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md))
    (hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K) {Bmin : ℤ} (hBmin : ∀ c ∈ Nd, Bmin ≤ c.1)
    (Δ h : ℕ) (halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
    (hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood Δ (Ms.goodP S SP c.1) h
      ⟨c.2.2, halive c hc⟩)
    (hstab : ∀ c ∈ Nd, ∀ z z', Ms.goodP S SP c.1 h ((Ms.blockComps S hA c.1 c.2.1).π z) →
      (Ms.blockComps S hA c.1 c.2.1).π z' = (Ms.blockComps S hA c.1 c.2.1).π z →
      z' ∈ (Ms.blockComps S hA c.1 c.2.1).F h z → z' ∈ (Ms.blockComps S hA c.1 c.2.1).E (h - Δ) z)
    (hdist : ∀ c (hc : c ∈ Nd) c' (hc' : c' ∈ Nd) (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1),
      c ≠ c' → (⟨c'.2.2, by rw [h1, h2]; exact halive c' hc'⟩ :
        Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) ∉
        (Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hc⟩)
    {k1 k2 : ℕ}
    (htype1 : ∀ c (hc : c ∈ Nd), v57FloorLog ((Ms.blockComps S hA c.1 c.2.1).labels
      ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ) ⟨c.2.2, halive c hc⟩)).card = k1)
    (htype2 : ∀ c ∈ Nd, v57FloorLog (Ms.predOfMode S hA Δ h c).card = k2) (dflt : Ms.Md) :
    ∃ rep : ℤ × (ℤ × ℤ) × Ms.Md → Ms.Md,
      (∀ c, rep c ∈ Ms.predOfMode S hA Δ h c) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' →
        Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' → rep c' = rep c) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' → rep c ≠ rep c' →
        Disjoint (Ms.predOfMode S hA Δ h c) (Ms.predOfMode S hA Δ h c')) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' → rep c ≠ rep c' →
        ∀ z z' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)), z.1 ∈ Ms.predOfMode S hA Δ h c →
          z'.1 ∈ Ms.predOfMode S hA Δ h c' → z ∉ (Ms.blockComps S hA c'.1 c'.2.1).F h z') := by
  set lt := nodeLt3 (Gd := Gd) Ms Nd
  set! d : ℤ × (ℤ × ℤ) × Ms.Md → ℕ := fun c => (c.1 - Bmin).toNat
  have hd : ∀ c c', lt c c' → d c < d c' := by
    intro c c' hcc'
    obtain ⟨hc, hc', -, hlt⟩ := hcc'
    have := hBmin c hc
    have := hBmin c' hc'
    simp only [d]
    omega
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  set E := Ms.predOfMode S hA Δ h
  have hne : ∀ c, (E c).Nonempty := by
    intro c
    by_cases hm : c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))
    · rw [show E c = _ from Ms.predOfMode_eq S hA Δ h hm]
      exact ⟨c.2.2, Finset.mem_map.mpr ⟨⟨c.2.2, hm⟩, ModeComponents.E_self _ _ _, rfl⟩⟩
    · simp only [E, predOfMode, dite_eq_right_of_eq_false (eq_false hm)]
      exact Finset.singleton_nonempty _
  -- linked predecessors along a path are nested
  have hlinked : ∀ c c', lt c c' → ∀ z z' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)),
      z.1 ∈ E c → z'.1 ∈ E c' → z ∈ (Ms.blockComps S hA c'.1 c'.2.1).F h z' → E c ⊆ E c' := by
    intro c c' hcc' z z' hz hz' hzF
    obtain ⟨hc, hc', hsub, hlt⟩ := hcc'
    have hUU := ancAt_block_subset S (hNd c hc) hlt.le hsub
    have hper := fun h' {x y : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))} =>
      Ms.blockComps_persist S hA (hNd c hc) (hNd c' hc') hlt.le hsub h' hUU (x := x) (y := y)
    set C := Ms.blockComps S hA c.1 c.2.1
    set C' := Ms.blockComps S hA c'.1 c'.2.1
    set! mc : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)) := ⟨c.2.2, halive c hc⟩
    set! mc' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)) := ⟨c'.2.2, halive c' hc'⟩
    have hEc : E c = (C.E (h - Δ) mc).map ⟨Subtype.val, Subtype.val_injective⟩ :=
      Ms.predOfMode_eq S hA Δ h (halive c hc)
    have hEc' : E c' = (C'.E (h - Δ) mc').map ⟨Subtype.val, Subtype.val_injective⟩ :=
      Ms.predOfMode_eq S hA Δ h (halive c' hc')
    rw [hEc] at hz ⊢
    rw [hEc'] at hz' ⊢
    obtain ⟨y1, hy1E, hy1⟩ := Finset.mem_map.mp hz
    obtain ⟨y2, hy2E, hy2⟩ := Finset.mem_map.mp hz'
    have hfy : Ms.aliveMap hUU y1 = z := Subtype.ext hy1
    have hy2z : y2 = z' := Subtype.ext hy2
    subst hy2z
    have hlink : Ms.aliveMap hUU mc ∈ C'.F h mc' := by
      have h1 : z ∈ C'.E (h - Δ) (Ms.aliveMap hUU mc) := by
        rw [← hfy]; exact (hper (h - Δ)).1 hy1E
      have h1' : Ms.aliveMap hUU mc ∈ C'.F h z := by
        have : Ms.aliveMap hUU mc ∈ C'.E (h - Δ) z := by
          rw [C'.E_comp _ _ z h1]; exact C'.E_self _ _
        exact C'.F_mono _ h _ (Nat.sub_le _ _) (C'.E_le_F _ _ this)
      have h2 : C'.F h z = C'.F h mc' := by
        rw [C'.F_comp h y2 z hzF]
        exact C'.F_comp h mc' y2
          (C'.F_mono _ h _ (Nat.sub_le _ _) (C'.E_le_F _ _ hy2E))
      rw [← h2]; exact h1'
    have htype : (C'.labels (C'.E (h - Δ) mc')).card <
        2 * (C.labels (C.E (h - Δ) mc)).card := by
      refine card_lt_two_mul_of_floorlog_eq ?_
        ((htype1 c hc).trans (htype1 c' hc').symm)
      exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (C.E_self _ _)⟩
    have hnest' := ModeComponents.predecessor_nesting C C' (Ms.aliveMap hUU)
      (fun x => by simp only [C, C', blockComps_π]; rfl)
      (fun h' x y hy => (hper h').1 hy) (fun h' x y hy => (hper h').2 hy) Δ (Ms.goodP S SP c'.1)
      (hstab c' hc') (C'.paperGood_to_good Δ (Ms.goodP S SP c'.1) (hgood c' hc')) hlink htype
    intro y hy
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_map.mpr ⟨Ms.aliveMap hUU y1,
      hnest' (Finset.mem_image_of_mem _ hy1), rfl⟩
  -- predecessors meeting along a path are nested
  have hnest : ∀ c c', lt c c' → (E c ∩ E c').Nonempty → E c ⊆ E c' := by
    intro c c' hcc' hmeet
    obtain ⟨y, hy⟩ := hmeet
    obtain ⟨hy1, hy2⟩ := Finset.mem_inter.mp hy
    have hEc' : E c' = ((Ms.blockComps S hA c'.1 c'.2.1).E (h - Δ)
        ⟨c'.2.2, halive c' hcc'.2.1⟩).map ⟨Subtype.val, Subtype.val_injective⟩ :=
      Ms.predOfMode_eq S hA Δ h (halive c' hcc'.2.1)
    have hy2' := hy2
    rw [hEc'] at hy2'
    obtain ⟨y2, hy2E, rfl⟩ := Finset.mem_map.mp hy2'
    exact hlinked c c' hcc' y2 y2 hy1 hy2
      ((Ms.blockComps S hA c'.1 c'.2.1).E_le_F h y2 (ModeComponents.E_self _ h y2))
  -- ancestors with meeting predecessors are comparable
  have hpath : ∀ a b c, lt a c → lt b c → (E a ∩ E b).Nonempty → a = b ∨ lt a b ∨ lt b a := by
    intro a b c hac hbc hmeet
    obtain ⟨ha, hc, hca, hlt⟩ := hac
    obtain ⟨hb, -, hcb, hlt'⟩ := hbc
    have hda := hNd a ha
    have hdb := hNd b hb
    rcases lt_trichotomy a.1 b.1 with h1 | h1 | h1
    · refine Or.inr (Or.inl ⟨ha, hb, ?_, h1⟩)
      exact dyadicGridCell_subset_of_common Gd hcb hca (by omega)
    · have hJ : a.2.1 = b.2.1 := dyadicGridCell_eq_of_meet Gd (by omega)
        ⟨_, hca (dyadicGridCell_left_mem Gd c.2.1.1 c.2.1.2),
          hcb (dyadicGridCell_left_mem Gd _ _)⟩
      by_cases hab : a = b
      · exact Or.inl hab
      · exfalso
        have hF := hdist a ha b hb h1 hJ hab
        set C := Ms.blockComps S hA a.1 a.2.1
        obtain ⟨y, hy⟩ := hmeet
        obtain ⟨hya, hyb⟩ := Finset.mem_inter.mp hy
        rw [show E a = _ from Ms.predOfMode_eq S hA Δ h (halive a ha)] at hya
        obtain ⟨y1, hy1, rfl⟩ := Finset.mem_map.mp hya
        have hEb : E b = (C.E (h - Δ) ⟨b.2.2, by rw [h1, hJ]; exact halive b hb⟩).map
            ⟨Subtype.val, Subtype.val_injective⟩ := by
          rw [show E b = _ from Ms.predOfMode_eq S hA Δ h (halive b hb)]
          obtain ⟨b1, b2, b3⟩ := b
          simp only at h1 hJ ⊢
          subst h1 hJ
          rfl
        rw [hEb] at hyb
        obtain ⟨y2, hy2, hyy⟩ := Finset.mem_map.mp hyb
        have hy12 : y2 = y1 := Subtype.ext hyy
        subst hy12
        -- `y2` lies in both CURRENT components
        have hfa : y2 ∈ C.F h ⟨a.2.2, halive a ha⟩ :=
          C.F_mono _ h _ (Nat.sub_le _ _) (C.E_le_F _ _ hy1)
        have hfb : y2 ∈ C.F h ⟨b.2.2, by rw [h1, hJ]; exact halive b hb⟩ :=
          C.F_mono _ h _ (Nat.sub_le _ _) (C.E_le_F _ _ hy2)
        apply hF
        have e1 := C.F_comp h _ _ hfa
        have e2 := C.F_comp h _ _ hfb
        rw [← e1, e2]
        exact C.E_le_F _ _ (C.E_self _ _)
    · refine Or.inr (Or.inr ⟨hb, ha, ?_, h1⟩)
      exact dyadicGridCell_subset_of_common Gd hca hcb (by omega)
  have hmaj : ∀ c c', lt c c' → E c ⊆ E c' → (E c').card < 2 * (E c).card := by
    intro c c' hcc' _
    exact card_lt_two_mul_of_floorlog_eq (Finset.card_pos.mpr (hne c))
      ((htype2 c hcc'.1).trans (htype2 c' hcc'.2.1).symm)
  refine ⟨hereditaryRep E lt d hd dflt, hereditaryRep_mem E lt d hd dflt hne,
    hereditaryRep_inherit' E lt d hd dflt hpath hnest hmaj, fun c c' hcc' hrep =>
      hereditaryRep_disjoint' E lt d hd dflt hpath hnest hmaj hcc' hrep,
    fun c c' hcc' hrep z z' hz hz' hzF => hrep (hereditaryRep_inherit' E lt d hd dflt hpath
      hnest hmaj c c' hcc' (hlinked c c' hcc' z z' hz hz' hzF)).symm⟩

open Classical in
/-- The first role type of a mode node: the base-1.1 floor-log size class of the number of primaries of its
PRE predecessor (blueprint line 2708, "fix ... all role types"). -/
noncomputable def paperNodeType1 (Δ h : ℕ) (c : ℤ × (ℤ × ℤ) × Ms.Md) : ℕ :=
  if hm : c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)) then
    v57FloorLog ((Ms.blockComps S hA c.1 c.2.1).labels
      ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ) ⟨c.2.2, hm⟩)).card
  else 0

/-- The second role type of a mode node: the base-1.1 floor-log size class of its predecessor. -/
noncomputable def paperNodeType2 (Δ h : ℕ) (c : ℤ × (ℤ × ℤ) × Ms.Md) : ℕ :=
  v57FloorLog (Ms.predOfMode S hA Δ h c).card

open Classical in
/-- Blueprint lines 2172-2191 with the role types fixed (`attempt_representatives_paper` on each type
class of nodes): there are representatives `rep k₁ k₂` for every type class, in the predecessors of
the nodes, inherited and separated along comparable nodes of the class. -/
theorem typed_representatives_paper (Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md))
    (hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K) {Bmin : ℤ} (hBmin : ∀ c ∈ Nd, Bmin ≤ c.1)
    (Δ h : ℕ) (halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
    (hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood Δ (Ms.goodP S SP c.1) h
      ⟨c.2.2, halive c hc⟩)
    (hstab : ∀ c ∈ Nd, ∀ z z', Ms.goodP S SP c.1 h ((Ms.blockComps S hA c.1 c.2.1).π z) →
      (Ms.blockComps S hA c.1 c.2.1).π z' = (Ms.blockComps S hA c.1 c.2.1).π z →
      z' ∈ (Ms.blockComps S hA c.1 c.2.1).F h z → z' ∈ (Ms.blockComps S hA c.1 c.2.1).E (h - Δ) z)
    (hdist : ∀ c (hc : c ∈ Nd) c' (hc' : c' ∈ Nd) (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1),
      c ≠ c' → (⟨c'.2.2, by rw [h1, h2]; exact halive c' hc'⟩ :
        Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) ∉
        (Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hc⟩) (dflt : Ms.Md) :
    ∃ rep : ℕ → ℕ → ℤ × (ℤ × ℤ) × Ms.Md → Ms.Md, ∀ k₁ k₂,
      let Nk := Nd.filter fun c => Ms.paperNodeType1 S hA Δ h c = k₁ ∧ Ms.paperNodeType2 S hA Δ h c = k₂
      (∀ c, rep k₁ k₂ c ∈ Ms.predOfMode S hA Δ h c) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nk c c' →
        Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' → rep k₁ k₂ c' = rep k₁ k₂ c) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nk c c' → rep k₁ k₂ c ≠ rep k₁ k₂ c' →
        Disjoint (Ms.predOfMode S hA Δ h c) (Ms.predOfMode S hA Δ h c')) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nk c c' → rep k₁ k₂ c ≠ rep k₁ k₂ c' →
        ∀ z z' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)), z.1 ∈ Ms.predOfMode S hA Δ h c →
          z'.1 ∈ Ms.predOfMode S hA Δ h c' → z ∉ (Ms.blockComps S hA c'.1 c'.2.1).F h z') := by
  have key : ∀ k₁ k₂ : ℕ, ∃ rep : ℤ × (ℤ × ℤ) × Ms.Md → Ms.Md,
      let Nk := Nd.filter fun c => Ms.paperNodeType1 S hA Δ h c = k₁ ∧ Ms.paperNodeType2 S hA Δ h c = k₂
      (∀ c, rep c ∈ Ms.predOfMode S hA Δ h c) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nk c c' →
        Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' → rep c' = rep c) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nk c c' → rep c ≠ rep c' →
        Disjoint (Ms.predOfMode S hA Δ h c) (Ms.predOfMode S hA Δ h c')) ∧
      (∀ c c', nodeLt3 (Gd := Gd) Ms Nk c c' → rep c ≠ rep c' →
        ∀ z z' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)), z.1 ∈ Ms.predOfMode S hA Δ h c →
          z'.1 ∈ Ms.predOfMode S hA Δ h c' → z ∉ (Ms.blockComps S hA c'.1 c'.2.1).F h z') := by
    intro k₁ k₂
    have hsub : ∀ c ∈ Nd.filter (fun c => Ms.paperNodeType1 S hA Δ h c = k₁ ∧
        Ms.paperNodeType2 S hA Δ h c = k₂), c ∈ Nd := fun c hc => (Finset.mem_filter.mp hc).1
    exact Ms.attempt_representatives_paper S hA SP _ (fun c hc => hNd c (hsub c hc))
      (fun c hc => hBmin c (hsub c hc)) Δ h (fun c hc => halive c (hsub c hc))
      (fun c hc => hgood c (hsub c hc)) (fun c hc => hstab c (hsub c hc))
      (fun c hc c' hc' h1 h2 hne => hdist c (hsub c hc) c' (hsub c' hc') h1 h2 hne)
      (k1 := k₁) (k2 := k₂)
      (fun c hc => by
        have h1 := (Finset.mem_filter.mp hc).2.1
        unfold paperNodeType1 at h1
        rwa [dite_eq_left_of_eq_true (eq_true (halive c (hsub c hc)))] at h1)
      (fun c hc => (Finset.mem_filter.mp hc).2.2) dflt
  choose rep hrep using key
  exact ⟨rep, hrep⟩


end Auto.ModeSystem

#print axioms OpenAI086.ReferenceV70.floorlog_ratio
#print axioms Auto.ModeComponents.paperGood_to_good
#print axioms Auto.ModeComponents.paper_good_same_predecessor
#print axioms Auto.ModeComponents.paper_good_minimal_pre
#print axioms Auto.ModeSystem.typed_representatives_paper

#print axioms Auto.ModeComponents.paper_core_minimal_pre
#print axioms Auto.ModeComponents.paper_core_bad_proportion
#print axioms Auto.ModeComponents.paper_core_current_coherence
#print axioms OpenAI086.ReferenceV70.card_lt_two_mul_of_floorlog_eq
#print axioms Auto.ModeSystem.attempt_representatives_paper
