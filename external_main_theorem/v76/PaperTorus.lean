/-
Adapted from the pinned Joris Roos reference, TrilinearHT/Auto/
Sec15_2bTorusSizeFourierTests.lean and Sec15_4VerificationCountingHypotheses.lean.
Copyright (c) 2026 Joris Roos; original authors: Claude. Apache-2.0.
V76: use actual paper masks and hereditary representatives. Uncompiled candidates.
-/
import ReferenceV75PaperFirstTops
import TrilinearHT.Auto.Sec15_4VerificationCountingHypotheses

set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace Auto
open MeasureTheory Metric OpenAI086.AdaptedV56 OpenAI086.ReferenceV70
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ModeComponents
variable {Mode P : Type*} [DecidableEq Mode] [DecidableEq P] (C : ModeComponents Mode P)

/-- Fixed-height version of good_same_predecessor. No stability at unused heights is assumed. -/
theorem paper_good_same_predecessor_at (Δ : ℕ) (goodP : ℕ → P → Prop)
    [∀ h, DecidablePred (goodP h)] {h : ℕ}
    (hstab : ∀ x x', goodP h (C.π x) → C.π x' = C.π x →
      x' ∈ C.F h x → x' ∈ C.E (h - Δ) x)
    {m m' : Mode} (hm : C.PaperGood Δ goodP h m) (hm' : C.PaperGood Δ goodP h m')
    (hmm' : m' ∈ C.F h m) : C.E (h - Δ) m = C.E (h - Δ) m' := by
  classical
  obtain ⟨hΔ, h1, h2⟩ := C.paperGood_to_good Δ goodP hm
  obtain ⟨-, h1', h2'⟩ := C.paperGood_to_good Δ goodP hm'
  have hF : C.F h m' = C.F h m := C.F_comp h m m' hmm'
  rw [hF] at h1' h2'
  set Ps := C.labels (C.F h m)
  have hsub : ∀ x, C.labels (C.E (h - Δ) x) ⊆ C.labels (C.F h x) := by
    intro x
    exact Finset.image_subset_image ((C.E_le_F _ x).trans (C.F_mono _ _ x (Nat.sub_le _ _)))
  have hA : C.labels (C.E (h - Δ) m) ⊆ Ps := hsub m
  have hB : C.labels (C.E (h - Δ) m') ⊆ Ps := by
    have := hsub m'; rwa [hF] at this
  set A := C.labels (C.E (h - Δ) m)
  set B := C.labels (C.E (h - Δ) m')
  set G := Ps.filter (goodP h)
  have hne : ((A ∩ B) ∩ G).Nonempty := by
    have hPs : 0 < Ps.card := by
      apply Finset.card_pos.mpr
      exact ⟨C.π m, Finset.mem_image_of_mem _ (C.E_le_F h m (C.E_self h m))⟩
    have h3 := card_inter_three_ge Ps A B G hA hB (Finset.filter_subset _ _)
    apply Finset.card_pos.mp
    omega
  obtain ⟨p, hp⟩ := hne
  obtain ⟨⟨hpA, hpB⟩, hpG⟩ := Finset.mem_inter.mp hp |>.imp_left Finset.mem_inter.mp
  have hpg := (Finset.mem_filter.mp hpG).2
  obtain ⟨x, hxE, rfl⟩ := Finset.mem_image.mp hpA
  obtain ⟨x', hx'E, hx'p⟩ := Finset.mem_image.mp hpB
  have hxF : x ∈ C.F h m := C.F_mono _ _ m (Nat.sub_le _ _) (C.E_le_F _ m hxE)
  have hx'F : x' ∈ C.F h m := hF ▸ C.F_mono _ _ m' (Nat.sub_le _ _) (C.E_le_F _ m' hx'E)
  have hjoin : x' ∈ C.E (h - Δ) x := by
    apply hstab x x' hpg hx'p
    rw [C.F_comp h m x hxF]; exact hx'F
  rw [C.E_eq_of_mem hxE, C.E_eq_of_mem hx'E, C.E_eq_of_mem hjoin]
end ModeComponents

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)

open Classical in
theorem mem_paperCompsAt {l : Fin 4} {G : bf.Grp} {I : ℤ × ℤ}
    {K : Finset (D.Ms l G).Md} (hK : K ∈ D.paperCompsAt l G I) :
    K ∈ (D.Ms l G).paperCoreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) := by
  unfold paperCompsAt at hK
  split_ifs at hK
  · exact hK
  · simp at hK

open Classical in
/-- Final CURRENT classes of the actual paper core components. -/
noncomputable def paperGoodCls (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (h : ℕ) :
    Finset (Finset (D.Ms j G).Md) :=
  ((D.paperCompsAt j G I).filter fun K => D.paperSlotGood G I j h (some K)).image
    fun K => (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K

open Classical in
/-- Coverage by a successful node, before division into representative type classes. -/
theorem paperGoodCls_cover {G : bf.Grp} {I : ℤ × ℤ} {j : Fin 4} {h : ℕ}
    {F : Finset (D.Ms j G).Md} (hF : F ∈ D.paperGoodCls G I j h) :
    ∃ x ∈ (D.Ms j G).paperSuccModes D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h,
      D.finCls G I j h x = F := by
  obtain ⟨K, hK, hKF⟩ := Finset.mem_image.mp hF
  obtain ⟨hKc, hg⟩ := Finset.mem_filter.mp hK
  obtain ⟨m, hmK, hmcore⟩ := (D.Ms j G).paperCoreComps_rep D.S D.hA D.SP
    (D.mem_paperCompsAt hKc)
  have hmg := ((D.Ms j G).paperCompGood_iff D.S D.hA D.SP hmK h).mp hg
  obtain ⟨x, hx, hxF⟩ := (D.Ms j G).paperSuccModes_cover D.S D.hA D.SP m hmcore hmg
  refine ⟨x, hx, ?_⟩
  rw [← hKF, hmK, (D.Ms j G).compClass_eq D.S D.hA _ _ h m]
  unfold finCls
  rw [hxF]

open Classical in
noncomputable def paperMaskComps (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ}
    (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    Finset (Finset (D.Ms j G).Md) :=
  (D.paperCompsAt j G I).filter fun K =>
    roleMask (D.paperSlotGood G I j) j asg w h (some K) ∧
    (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K = F

open Classical in
noncomputable def paperMaskSel (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ}
    (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :=
  Finset.univ.filter fun x => ∃ K ∈ D.paperMaskComps G I j asg w h F, x.1 ∈ K

open Classical in
theorem paperMaskComps_disjoint (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ}
    (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    Set.PairwiseDisjoint (D.paperMaskComps G I j asg w h F : Set (Finset (D.Ms j G).Md)) id := by
  refine ((D.Ms j G).allComps_pairwiseDisjoint D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).subset ?_
  intro K hK
  exact (Finset.mem_sdiff.mp (D.mem_paperCompsAt (Finset.mem_filter.mp (Finset.mem_coe.mp hK)).1)).1

open Classical in
theorem paperMaskSel_map (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ}
    (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    (D.paperMaskSel G I j asg w h F).map ⟨Subtype.val, Subtype.val_injective⟩ =
      (D.paperMaskComps G I j asg w h F).biUnion id := by
  ext m
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_biUnion, id]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  · rintro ⟨K, hK, hmK⟩
    obtain ⟨x, hKx, -⟩ := (D.Ms j G).paperCoreComps_rep D.S D.hA D.SP
      (D.mem_paperCompsAt (Finset.mem_filter.mp hK).1)
    rw [hKx] at hmK
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hmK
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, K, hK, hKx.symm ▸ Finset.mem_map_of_mem _ hy⟩, rfl⟩

open Classical in
/-- Grouping by final class preserves the actual core subtotal. -/
theorem paper_masked_subtotal (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ}
    (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    ∑ K ∈ D.paperMaskComps G I j asg w h F, D.compSub j G I K =
      D.compSub j G I ((D.paperMaskSel G I j asg w h F).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  rw [D.paperMaskSel_map]
  exact D.sum_compSub j G I _ (D.paperMaskComps_disjoint G I j asg w h F)

open Classical in
/-- The hereditary representative of a successful node is alive and lies in its predecessor. -/
theorem paper_rep_anchor (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {h : ℕ}
    (R : (D.Ms j G).PaperRepClass D.S D.hA D.SP D.SP.Δ h)
    (m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hm : (A.blkStart D.S.K I.1, D.preAt I, m.1) ∈ R.Nd) :
    ∃ a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)),
      a.1 = R.rep (A.blkStart D.S.K I.1, D.preAt I, m.1) ∧
      a ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E
        (h - D.SP.Δ) m := by
  have ha := R.hrep (A.blkStart D.S.K I.1, D.preAt I, m.1)
  rw [(D.Ms j G).predOfMode_eq D.S D.hA D.SP.Δ h
    (c := (A.blkStart D.S.K I.1, D.preAt I, m.1)) m.2] at ha
  obtain ⟨a, ha, he⟩ := Finset.mem_map.mp ha
  exact ⟨a, he, ha⟩

open Classical in
/-- Selected modes lie in the PRE predecessor of the actual paper representative. -/
theorem paperMaskSel_pred (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {h : ℕ}
    (R : (D.Ms j G).PaperRepClass D.S D.hA D.SP D.SP.Δ h)
    (m a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hm : (A.blkStart D.S.K I.1, D.preAt I, m.1) ∈ R.Nd)
    (ha : a ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E
      (h - D.SP.Δ) m) {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) :
    ∀ x ∈ D.paperMaskSel G I j asg w h (D.finCls G I j h m),
      x ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E
        (h - D.SP.Δ) a := by
  intro x hx
  set C := (D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)
  obtain ⟨K, hK, hxK⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hKc, hmask, hcls⟩ := Finset.mem_filter.mp hK
  obtain ⟨y, hyK, hyg⟩ := (hmask.1 : (D.Ms j G).paperCompGood D.S D.hA D.SP
    (A.blkStart D.S.K I.1) (D.preAt I) h K)
  rw [hyK, (D.Ms j G).compClass_eq D.S D.hA _ _ h y] at hcls
  change (C.F h y).map ⟨Subtype.val, Subtype.val_injective⟩ =
    (C.F h m).map ⟨Subtype.val, Subtype.val_injective⟩ at hcls
  have hF : C.F h y = C.F h m := Finset.map_injective _ hcls
  have hym : y ∈ C.F h m := hF ▸ C.mem_F_self h y
  have hmg : C.PaperGood D.SP.Δ ((D.Ms j G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m :=
    R.hgood _ hm
  have he := C.paper_good_same_predecessor_at D.SP.Δ _ (R.hstab _ hm) hmg hyg hym
  rw [hyK] at hxK
  obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hxK
  have hx0 : x ∈ C.E 0 y := by rw [← Subtype.val_injective hzx]; exact hz
  rw [C.E_comp (h - D.SP.Δ) m a ha, he]
  exact C.E_mono 0 (h - D.SP.Δ) y (Nat.zero_le _) hx0

open Classical in
/-- Actual torus reduction for the selected paper modes. -/
theorem paper_mask_torus (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {h : ℕ}
    (R : (D.Ms j G).PaperRepClass D.S D.hA D.SP D.SP.Δ h)
    (m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hm : (A.blkStart D.S.K I.1, D.preAt I, m.1) ∈ R.Nd)
    (hQ : 1 ≤ D.S.Q0) (hD : 2 ≤ D.S.Dstar)
    (hcard : (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : (D.Ms j G).Λ ≤ D.S.Dstar) (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K)
    {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) {xs : ℝ}
    (hxs : xs ∈ dyadicGridCell A.G I.1 I.2) :
    ∃ a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)),
      a.1 = R.rep (A.blkStart D.S.K I.1, D.preAt I, m.1) ∧
      ∃ ns, D.TorusFormAt G I j (h - D.SP.Δ) xs
        (D.paperMaskSel G I j asg w h (D.finCls G I j h m)) ns a := by
  obtain ⟨a, ha, hap⟩ := D.paper_rep_anchor G I j R m hm
  have hf := D.paperMaskSel_pred G I j R m a hm hap asg w
  have hb := blkStart_bounds D.hK I.1 (A := A)
  obtain ⟨ns, hn, hform⟩ := (D.Ms j G).cell_torus_form D.S D.hA (b := A.blkStart D.S.K I.1)
    (J := D.preAt I) rfl (D.subset_preAt I) hb.1 a
    (D.paperMaskSel G I j asg w h (D.finCls G I j h m))
    (fun x hx => hf x hx) (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) hxs hQ hD
    hcard hΛ hK
  refine ⟨a, ha, ns, fun x hx i => (hn x hx i).trans ?_, hform⟩
  have hE : 0 ≤ D.S.Eh (h - D.SP.Δ) := by
    unfold ModeSchedule.Eh
    exact pow_nonneg (le_trans (by norm_num) D.hA) _
  have hc : (Fintype.card ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))) : ℝ) ≤ D.S.Dstar := by
    rw [Fintype.card_coe]; exact hcard
  exact mul_le_mul_of_nonneg_right hc hE

end SideInput
end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.mem_paperCompsAt
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperGoodCls_cover
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperMaskComps_disjoint
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperMaskSel_map
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_masked_subtotal
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_rep_anchor
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperMaskSel_pred
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_mask_torus

#print axioms Auto.ModeComponents.paper_good_same_predecessor_at
