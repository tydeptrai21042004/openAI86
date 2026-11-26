/-
V74 source candidate, adapted from TrilinearHT/Auto/Sec14_5bExportedSideEstimate.lean.
Copyright (c) 2026 Joris Roos; original authors: Claude. Apache-2.0.
The actual paper-specific side state replaces the older ratio-based side state.
The U slot stays augmented for the fixed-stack argument; the local form only
sees its physical coordinate. No Lean elaboration has been performed.
-/
import ReferenceV73PaperRollingEnergy
import TrilinearHT.Auto.Sec14_5bExportedSideEstimate

set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)


open Classical in
noncomputable def paperWr (l : Fin 4) (G : bf.Grp) (b : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  D.Zr l G b - fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.frozenZ l (D.cat l) (D.mbs l) G
    (D.Lf.role l) (D.Lf.layers l) (b - 4 * D.S.K)) +
    fp.physMain (D.Ms l G).Md ((D.Ms l G).paperBlockSide D.S D.hA D.SP b (fp.retainedV G b D.S.K)
      (D.c l G b))

open Classical in
noncomputable def paperGs (l : Fin 4) (G : bf.Grp) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  fp.paperSideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l) (D.Lf.layers l) D.S D.hA D.SP
    (D.c l G (A.blkStart D.S.K h)) (A.blkStart D.S.K h) h

open Classical in
theorem paperGs_eq (l : Fin 4) (G : bf.Grp) (h : ℤ) :
    D.paperGs l G h = D.Zr l G h - D.Zr l G (A.blkStart D.S.K h) + D.paperWr l G (A.blkStart D.S.K h) := by
  unfold paperGs paperSideState paperWr Zr
  abel

open Classical in
theorem paperGs_range (l : Fin 4) (G : bf.Grp) (h : ℤ) :
    D.paperGs l G h ∈ LinearMap.range (colRelabel (bf.rv fp.Mc (D.cat l))).toLinearMap := by
  unfold paperGs paperSideState
  exact Submodule.add_mem _ (Submodule.sub_mem _ (fp.physMain_mem_range _ _)
    (fp.physMain_mem_range _ _)) (fp.physMain_mem_range _ _)

open Classical in
noncomputable def paperToLeaf : fp.SideLeafM where
  cat := D.cat
  mbs := D.mbs
  Lf := D.Lf
  u := D.u
  K := D.S.K
  hK := D.hK
  xin := fun l I => if D.u = some l then bf.Ucol fp.Mc l I else bf.basicIn fp.Mc l I
  xin_basic := fun l hl I => by simp only [hl, ite_false]
  sv := fun l G I => if D.u = some l then
      fp.ballFilt l (D.cat l) I G (D.Lf.role l)
        (layerOp (fun m => fp.cumFilt l (D.cat l) I m) (D.Lf.layers l) (bf.Ucol fp.Mc l I))
    else columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
      (D.paperGs l G I.1)
  gside := D.paperGs
  sv_eq := fun l hl G I _ => by simp only [hl, ite_false]
  gside_range := fun l _ G h => D.paperGs_range l G h
  Z := D.Zr
  Wb := D.paperWr
  gside_eq := fun l _ G h => D.paperGs_eq l G h
  sv_u := fun l hl G I => by simp only [hl, ite_true]

open Classical in
noncomputable def paperToLeafQ (qG : bf.Grp → ℕ) : fp.SideLeafM where
  cat := D.cat
  mbs := D.mbs
  Lf := D.Lf
  u := D.u
  K := D.S.K
  hK := D.hK
  xin := D.paperToLeaf.xin
  xin_basic := D.paperToLeaf.xin_basic
  sv := fun l G I => (D.withQ0 (qG G)).paperToLeaf.sv l G I
  gside := fun l G h => (D.withQ0 (qG G)).paperGs l G h
  sv_eq := fun l hl G I hI => (D.withQ0 (qG G)).paperToLeaf.sv_eq l hl G I hI
  gside_range := fun l _ G h => (D.withQ0 (qG G)).paperGs_range l G h
  Z := D.Zr
  Wb := fun l G b => (D.withQ0 (qG G)).paperWr l G b
  gside_eq := fun l _ G h => (D.withQ0 (qG G)).paperGs_eq l G h
  sv_u := fun l hl G I => (D.withQ0 (qG G)).paperToLeaf.sv_u l hl G I

open Classical in
theorem paperToLeafQ_sv (qG : bf.Grp → ℕ) (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    (D.paperToLeafQ qG).sv l G I = (D.withQ0 (qG G)).paperToLeaf.sv l G I := rfl

open Classical in
theorem paperToLeafQ_out (qG : bf.Grp → ℕ) (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    (D.paperToLeafQ qG).out l G I = (D.withQ0 (qG G)).paperToLeaf.out l G I := by
  unfold SideLeafM.out
  rfl

open Classical in
theorem paperGs_nat (l : Fin 4) (G : bf.Grp) (t : ℕ) :
    D.paperGs l G (A.R.1 + t) = fp.paperSideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l)
      (D.Lf.layers l) D.S D.hA D.SP (D.c l G (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)))
      (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)) (A.R.1 + t) := by
  unfold paperGs
  rw [blkStart_nat]

open Classical in
theorem paperToLeaf_sv_basic {l : Fin 4} (hl : D.u ≠ some l) (G : bf.Grp) (I : ℤ × ℤ) :
    D.paperToLeaf.sv l G I = columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (D.paperGs l G I.1) := by
  change (if D.u = some l then _ else _) = _
  simp only [hl, ↓reduceIte]

open Classical in
theorem paperToLeaf_sv_U {l : Fin 4} (hl : D.u = some l) (G : bf.Grp) (I : ℤ × ℤ) :
    D.paperToLeaf.sv l G I = fp.ballFilt l (D.cat l) I G (D.Lf.role l)
      (layerOp (fun m => fp.cumFilt l (D.cat l) I m) (D.Lf.layers l) (bf.Ucol fp.Mc l I)) := by
  change (if D.u = some l then _ else _) = _
  simp only [hl, ↓reduceIte]

open Classical in
theorem paperToLeaf_sv_basic_exact (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ)
    (hl : D.u ≠ some l) :
    D.paperToLeaf.sv l G I = D.paperSideAt l G I := by
  rw [D.paperToLeaf_sv_basic hl, D.paperSideAt_eq_restrict_state l G I hl] <;> rfl

open Classical in
theorem paperCoreAt_physical (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    fp.physMain (bf.Lab ⊕ Fin fp.Mc) (D.paperCoreAt l G I) = D.paperCoreAt l G I := by
  unfold paperCoreAt
  split_ifs
  · exact map_zero _
  · rw [← physEmbed_restrict, fp.physMain_physMain]

open Classical in
theorem paperToLeaf_sv_physical (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    fp.physMain (bf.Lab ⊕ Fin fp.Mc) (D.paperToLeaf.sv l G I) = D.paperSideAt l G I := by
  by_cases hl : D.u = some l
  · unfold paperSideAt coreAt paperCoreAt
    simp only [hl, if_true, add_zero, sub_zero] <;> rfl
  · rw [D.paperToLeaf_sv_basic_exact l G I hl]
    unfold paperSideAt
    rw [map_sub, map_add, fp.physMain_physMain, D.physMain_coreAt, D.paperCoreAt_physical]

/-- The per-group schedule version used by the side estimate. -/
theorem paperToLeafQ_sv_physical (qG : bf.Grp → ℕ) (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    fp.physMain (bf.Lab ⊕ Fin fp.Mc) ((D.paperToLeafQ qG).sv l G I) =
      (D.withQ0 (qG G)).paperSideAt l G I :=
  (D.withQ0 (qG G)).paperToLeaf_sv_physical l G I


open Classical in
theorem paper_V_sum_le (qG : bf.Grp → ℕ) (l : Fin 4) (gset : Finset bf.Grp) (Bn : ℕ) (Sd : Finset ℕ)
    (hSd : ∀ t ∈ Sd, ∃ β < Bn, t = D.S.K * β) :
    ∑ b ∈ Sd, ∑ G : {G // G ∈ gset}, ‖(D.Ms l G.1).paperBlockSide (D.S.withQ0 (qG G.1)) D.hA D.SP (A.R.1
        + (b : ℤ))
        (fp.retainedV G.1 (A.R.1 + (b : ℤ)) D.S.K) (D.c l G.1 (A.R.1 + (b : ℤ)))‖ ^ 2 ≤
      ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).paperBlockSide (D.S.withQ0 (qG G)) D.hA D.SP
        (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
        (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 := by
  have hK := D.hK
  set! f : ℕ → ℝ := fun b => ∑ G ∈ gset, ‖(D.Ms l G).paperBlockSide (D.S.withQ0 (qG G)) D.hA D.SP (A.R.1
      + (b : ℤ))
    (fp.retainedV G (A.R.1 + (b : ℤ)) D.S.K) (D.c l G (A.R.1 + (b : ℤ)))‖ ^ 2 with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc _ = ∑ b ∈ Sd, f b := Finset.sum_congr rfl fun b _ => Finset.sum_coe_sort gset _
    _ ≤ ∑ b ∈ (Finset.range Bn).image (fun β => D.S.K * β), f b := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun b _ _ => hf0 b
        obtain ⟨β, hβ, rfl⟩ := hSd t ht
        exact Finset.mem_image.mpr ⟨β, Finset.mem_range.mpr hβ, rfl⟩
    _ = ∑ β ∈ Finset.range Bn, f (D.S.K * β) :=
        Finset.sum_image fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy
    _ = _ := by
        rw [hf]
        exact Finset.sum_comm

open Classical in
theorem paper_basic_side_energy (qG : bf.Grp → ℕ) (hanc : A.AncClosed) (hne : A.cells.Nonempty) {l : Fin
    4}
    (hl : D.u ≠ some l) (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells) (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (k Bn : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I) (hBn : ∀ I ∈ S, (D.paperToLeafQ qG).bk I < Bn)
    (B : (D.paperToLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : ℝ}
    (hlin : ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).paperBlockSide (D.S.withQ0 (qG G)) D.hA D.SP
        (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
        (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ Vl * dyadicGridLength A.G A.R.1) :
    ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2 ≤ D.sideB cc kk Vl := by
  have hK := D.hK
  have hdep : ∀ I ∈ S, A.R.1 ≤ I.1 := fun I hI =>
    dyadicGridCell_depth_le_of_subset A.G I A.R (A.sub I (hS hI))
  set! Sd : Finset ℕ := S.image (fun I => (I.1 - A.R.1).toNat) with hSd_def
  set! Ec : {G // G ∈ gset} → ℕ → Finset (ℤ × ℤ) := fun G t =>
    S.filter fun I => I.1 = A.R.1 + t ∧ G.1 ∈ gs I with hEc_def
  have hbud := fp.paper_sideState_budget l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) hanc hne
    (ι := {G // G ∈ gset}) Subtype.val Subtype.val_injective k (D.Lf.role l) (B.hPH l)
    (D.Lf.layers l) D.S D.hA D.SP D.hK (fun G => D.Ms l G.1) (fun G => qG G.1) (fun G => D.c l G.1)
        Sd
    (fun t ht => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.le_sup (f := fun I => (I.1 - A.R.1).toNat) (hS hI))
    Ec (fun G t I hI => by
      obtain ⟨hIS, hIt, -⟩ := Finset.mem_filter.mp hI
      exact ⟨hS hIS, hIt⟩)
    (fun G t I hI => by
      obtain ⟨hIS, -, hG⟩ := Finset.mem_filter.mp hI
      exact hcertS I hIS G.1 hG) hroot' hτ' hτ1 hHed (B.hN l) hτN cc hc hk (hDm l) hDb (hLs l)
  have heq := cell_budget_eq A.G S (fun (G : {G // G ∈ gset}) h => (D.withQ0 (qG G.1)).paperGs l G.1 h)
    (fun G I => G.1 ∈ gs I) Sd A.R.1 Ec (fun G t => rfl) (fun I hI => ⟨(I.1 - A.R.1).toNat,
      Finset.mem_image_of_mem _ hI, by have := hdep I hI; omega⟩)
  calc ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2
      = ∑ I ∈ S, ∑ G : {G // G ∈ gset}, (if G.1 ∈ gs I then
          ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
            ((D.withQ0 (qG G.1)).paperGs l G.1 I.1)‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun I hI => ?_
        rw [sum_sub_eq_ite (hgs I hI)]
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [D.paperToLeafQ_sv, (D.withQ0 (qG G.1)).paperToLeaf_sv_basic hl]
    _ = ∑ t ∈ Sd, ∑ G : {G // G ∈ gset}, ‖columnL2Restriction
          (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
          ((D.withQ0 (qG G.1)).paperGs l G.1 (A.R.1 + t))‖ ^ 2 := by
        refine Eq.trans ?_ heq
        refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun G _ => ?_
        split_ifs <;> rfl
    _ = ∑ t ∈ Sd, ∑ G : {G // G ∈ gset}, ‖columnL2Restriction
          (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
          (fp.paperSideState (D.Ms l G.1) l (D.cat l) (D.mbs l) G.1 (D.Lf.role l) (D.Lf.layers l)
              (D.S.withQ0 (qG G.1))
            D.hA D.SP (D.c l G.1 (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)))
            (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun G _ => ?_
        rw [(D.withQ0 (qG G.1)).paperGs_nat]; rfl
    _ ≤ _ := hbud
    _ ≤ D.sideB cc kk Vl := by
        unfold sideB
        have hV := D.paper_V_sum_le qG l gset Bn (Sd.image fun t => D.S.K * (t / D.S.K)) (fun t' ht' => by
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
          refine ⟨(I.1 - A.R.1).toNat / D.S.K, ?_, rfl⟩
          have h1 := hBn I hI
          change ((I.1 - A.R.1) / D.S.K).toNat < Bn at h1
          rwa [toNat_ediv_eq (by have := hdep I hI; omega)] at h1)
        gcongr
        exact hV.trans hlin

open Classical in
theorem paper_block_energy (qG : bf.Grp → ℕ) (hanc : A.AncClosed) (hne : A.cells.Nonempty) {l : Fin 4}
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells) (gs : ℤ × ℤ → Finset bf.Grp)
    (gset : Finset bf.Grp) (k Bn : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I) (hBn : ∀ I ∈ S, (D.paperToLeafQ qG).bk I < Bn)
    (B : (D.paperToLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : ℝ}
    (hlin : ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).paperBlockSide (D.S.withQ0 (qG G)) D.hA D.SP
        (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) D.S.K)
        (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤ Vl * dyadicGridLength A.G A.R.1) :
    ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ (D.paperToLeafQ qG).bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + (((D.paperToLeafQ qG).K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1
            J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      ((D.paperToLeafQ qG).Wb l G (A.R.1 + (((D.paperToLeafQ qG).K * β : ℕ) : ℤ)))‖ ^ 2 ≤ sideB0 A cc kk Vl :=
          by
  have hK := D.hK
  have hdep : ∀ I ∈ S, A.R.1 ≤ I.1 := fun I hI =>
    dyadicGridCell_depth_le_of_subset A.G I A.R (A.sub I (hS hI))
  have hbkle : ∀ I ∈ S, D.S.K * (D.paperToLeafQ qG).bk I ≤ (I.1 - A.R.1).toNat := by
    intro I hI
    change D.S.K * ((I.1 - A.R.1) / D.S.K).toNat ≤ _
    rw [toNat_ediv_eq (by have := hdep I hI; omega)]
    exact Nat.mul_div_le _ _
  have hle : ∀ I ∈ S, A.R.1 + ((D.S.K * (D.paperToLeafQ qG).bk I : ℕ) : ℤ) ≤ I.1 := by
    intro I hI
    have h1 := hbkle I hI
    have h2 : (((I.1 - A.R.1).toNat : ℕ) : ℤ) = I.1 - A.R.1 :=
      Int.toNat_of_nonneg (by have := hdep I hI; omega)
    have h3 : ((D.S.K * (D.paperToLeafQ qG).bk I : ℕ) : ℤ) ≤ ((I.1 - A.R.1).toNat : ℤ) := by
      exact_mod_cast h1
    omega
  set! Sd : Finset ℕ := S.image (fun I => D.S.K * (D.paperToLeafQ qG).bk I) with hSd_def
  set! Ec : bf.Grp → ℕ → Finset (ℤ × ℤ) := fun G t =>
    (S.filter fun I => G ∈ gs I ∧ D.S.K * (D.paperToLeafQ qG).bk I = t).image
      (fun I => ancAt A.G I (A.R.1 + t)) with hEc_def
  have hEc : ∀ (G : {G // G ∈ gset}) t, ∀ J ∈ Ec G.1 t, J ∈ A.cells ∧ J.1 = A.R.1 + t := by
    intro G t J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, -, ht⟩ := Finset.mem_filter.mp hI
    have h1 := hle I hIS
    rw [ht] at h1
    exact ⟨hanc I (hS hIS) _ (subset_ancAt A.G I h1)
      (ancAt_subset (A.sub I (hS hIS)) (by omega)), rfl⟩
  have hcert : ∀ (G : {G // G ∈ gset}) t, ∀ J ∈ Ec G.1 t, fp.Cert k G.1 J := by
    intro G t J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hG, ht⟩ := Finset.mem_filter.mp hI
    have h1 := hle I hIS
    rw [ht] at h1
    exact (hcertS I hIS G.1 hG).mono fp (subset_ancAt A.G I h1)
  have hbud := fp.paper_sideState_budget_blocks l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) hanc
    hne (ι := {G // G ∈ gset}) Subtype.val Subtype.val_injective k (D.Lf.role l) (B.hPH l)
    (D.Lf.layers l) D.S D.hA D.SP D.hK (fun G => D.Ms l G.1) (fun G => qG G.1) (fun G => D.c l G.1)
        Sd
    (fun t ht => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
      exact (hbkle I hI).trans (Finset.le_sup (f := fun I => (I.1 - A.R.1).toNat) (hS hI)))
    (fun t ht => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
      exact Dvd.intro _ rfl)
    (fun G t => Ec G.1 t) hEc hcert hroot' hτ' hτ1 hHed (B.hN l) hτN cc hc hk (hDm l) hDb (hLs l)
  set! H : bf.Grp → ℕ → ℝ := fun G t => ‖columnL2Restriction
    (⋃ J ∈ Ec G t, dyadicGridCell A.G J.1 J.2)
    (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
    (fp.paperSideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l) (D.Lf.layers l) (D.S.withQ0
        (qG G))
      D.hA D.SP (D.c l G (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)))
      (A.R.1 + ((D.S.K * (t / D.S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 with hH
  have hsub : S.image (D.paperToLeafQ qG).bk ⊆ Finset.range Bn := fun β hβ => by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hβ
    exact Finset.mem_range.mpr (hBn I hI)
  have hterm : ∀ G β, ‖columnL2Restriction
      (⋃ J ∈ (S.filter fun I => G ∈ gs I ∧ (D.paperToLeafQ qG).bk I = β).image
        (fun I => ancAt A.G I (A.R.1 + (((D.paperToLeafQ qG).K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1
            J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      ((D.paperToLeafQ qG).Wb l G (A.R.1 + (((D.paperToLeafQ qG).K * β : ℕ) : ℤ)))‖ ^ 2 = H G (D.S.K * β) :=
          by
    intro G β
    have e1 : D.S.K * β / D.S.K = β := Nat.mul_div_cancel_left β (by omega)
    have e2 : (S.filter fun I => G ∈ gs I ∧ D.S.K * (D.paperToLeafQ qG).bk I = D.S.K * β) =
        S.filter fun I => G ∈ gs I ∧ (D.paperToLeafQ qG).bk I = β := by
      refine Finset.filter_congr fun I _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Nat.eq_of_mul_eq_mul_left (by omega) h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]⟩
    simp only [hH, hEc_def, e1, e2]
    rfl
  calc _ = ∑ G ∈ gset, ∑ β ∈ S.image (D.paperToLeafQ qG).bk, H G (D.S.K * β) := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [← Finset.sum_subset hsub fun β _ hβ => ?_]
        · exact Finset.sum_congr rfl fun β _ => hterm G β
        · refine norm_sq_restrict_biUnion_empty A.G _ ?_ _
          rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
          rintro I hI ⟨-, hb⟩
          exact hβ (Finset.mem_image.mpr ⟨I, hI, hb⟩)
    _ = ∑ G ∈ gset, ∑ t ∈ Sd, H G t := by
        refine Finset.sum_congr rfl fun G _ => ?_
        have e : Sd = (S.image (D.paperToLeafQ qG).bk).image (fun β => D.S.K * β) := by
          rw [Finset.image_image]; rfl
        rw [e, Finset.sum_image fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (by omega) hxy]
    _ = ∑ t ∈ Sd, ∑ G : {G // G ∈ gset}, H G.1 t := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => (Finset.sum_coe_sort gset _).symm
    _ ≤ _ := hbud
    _ ≤ sideB0 A cc kk Vl := by
        unfold sideB0
        have hV := D.paper_V_sum_le qG l gset Bn Sd (fun t ht => by
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
          exact ⟨(D.paperToLeafQ qG).bk I, hBn I hI, rfl⟩)
        gcongr
        exact hV.trans hlin

open Classical in
theorem paper_U_side_energy (qG : bf.Grp → ℕ) {l : Fin 4} (hl : D.u = some l)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ A.cells)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset) (k : ℕ)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I) (B : (D.paperToLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) :
    ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2 ≤ 2 * ∑ I ∈ S, ‖bf.Ucol fp.Mc l I‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  have h := fp.cell_bessel l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) gset k
    (D.Lf.role l) (B.hPH l) (D.Lf.layers l) (hS hI) (gs I) (hgs I hI) (hcertS I hI) hroot' hτ'
    hτ1 hHed (B.hN l) (bf.Ucol fp.Mc l I) (bf.Ucol_mem_range fp.Mc (D.cat l) l I)
    (bf.restrict_Ucol fp.Mc l I)
  have hC : 1 + τ' * B.N * A.colBudget ^ 2 ≤ 2 := by linarith
  calc ∑ G ∈ gs I, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2
      = ∑ G ∈ gs I, ‖fp.ballFilt l (D.cat l) I G (D.Lf.role l)
          (layerOp (fun m => fp.cumFilt l (D.cat l) I m) (D.Lf.layers l)
            (bf.Ucol fp.Mc l I))‖ ^ 2 :=
        Finset.sum_congr rfl fun G _ => by rw [D.paperToLeafQ_sv, (D.withQ0 (qG G)).paperToLeaf_sv_U hl]; rfl
    _ ≤ _ := h
    _ ≤ 2 * ‖bf.Ucol fp.Mc l I‖ ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)

open Classical in
theorem paper_toLeaf_cap (qG : bf.Grp → ℕ) (hanc : A.AncClosed) (hne : A.cells.Nonempty) (gset : Finset
    bf.Grp) (k : ℕ)
    (B : (D.paperToLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * (D.mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) (l : Fin 4) :
    A.VarCap gset ((D.paperToLeafQ qG).Z l) (fun G J => fp.Cert k G J) (capV A cc kk) := by
  intro ι _ r t hrt hdis htd Ec hEc
  exact fp.varCap_basicOut l (D.cat l) (B.hT l) (B.htag l) (B.dv l) (D.mbs l) hanc hne gset k
    (D.Lf.role l) (B.hPH l) (D.Lf.layers l) hroot' hτ' hτ1 hHed (B.hN l) hτN cc hc hk (hDm l) hDb
    (hLs l) r t hrt hdis htd Ec hEc

open Classical in
theorem paper_side_estimate (qG : bf.Grp → ℕ) {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (hanc : A.AncClosed)
    (hne : A.cells.Nonempty)
    {Nd N : ℕ} (hKNd : A.DepthWin Nd) (hKN : (D.paperToLeafQ qG).K ≤ 2 ^ N) (S : Finset (ℤ × ℤ)) (hS : S
        ⊆
        A.cells)
    (hroot : ∀ I ∈ S, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ S, gs I ⊆ gset)
    (Lp Jm Bn k : ℕ) (hBn : ∀ I ∈ S, (D.paperToLeafQ qG).bk I < Bn)
    (hLp : ∀ l, ((D.paperToLeafQ qG).pe l).length ≤ Lp)
    (hJm : ∀ c d i i',
      ((D.paperToLeafQ qG).desc c d ((D.paperToLeafQ qG).tOf c i) ((D.paperToLeafQ qG).tOf d i')).length ≤ Jm)
    (Act : Finset (ℤ × ℤ)) (hact : ∀ I ∈ S, I ∈ Act ∧ ∀ G ∈ gs I, G ∈ fp.groupsAt I k)
    {Mp : ℝ} (hMp : ∀ y, ((Act.filter fun c => y ∈ dyadicGridCell A.G c.1 c.2).card : ℝ) ≤ Mp)
    (hcertS : ∀ I ∈ S, ∀ G ∈ gs I, fp.Cert k G I)
    {τ cF C₀ B₀ : ℝ} (hτ : 0 ≤ τ) (hcF : 0 ≤ cF) (hC₀ : 0 < C₀) (hB₀ : 0 ≤ B₀)
    (hpair : ∀ I ∈ S, ∀ c d, c ≠ d → (D.paperToLeafQ qG).u ≠ some c → (D.paperToLeafQ qG).u ≠ some d →
      PairSmall (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) c d
        (A.Y I c) (A.Y I d) τ)
    (hfar : ∀ I ∈ S, ∀ G ∈ gs I, ∀ a b c d, (D.paperToLeafQ qG).Val a b c d → ¬ (D.paperToLeafQ qG).Ucase c d
        →
      ∀ t ∈ (D.paperToLeafQ qG).pe c, ∀ t' ∈ (D.paperToLeafQ qG).pe d,
      ‖chainDefectSel (fp.Λc I) fp.P a c d (fun l => (D.paperToLeafQ qG).sv l G I) (bf.basicIn fp.Mc c I)
        (bf.basicIn fp.Mc d I) (fun p q => q + 2 < p ∨ p + 2 < q)
        (fp.mergeStepsM (D.paperToLeafQ qG).cat a c d (fp.Lc + 5) I
          (fp.slotFiltM G ((D.paperToLeafQ qG).Lf.role c) I t.2) (fp.slotFiltM G ((D.paperToLeafQ qG).Lf.role
              d) I t'.2))
        ((D.paperToLeafQ qG).sv a G I)‖ ≤ cF * (D.paperToLeafQ qG).ns a G I * (D.paperToLeafQ qG).ns b G I)
    (hbas : ∀ J ∈ A.cells, ∀ l, (D.paperToLeafQ qG).u ≠ some l →
      ‖bf.basicIn fp.Mc l J‖ ≤ C₀ * Real.sqrt (dyadicGridLength A.G J.1))
    (hout : ∀ I ∈ S, ∀ G ∈ gs I, ∀ l,
      ‖(D.paperToLeafQ qG).out l G I‖ ≤ B₀ * Real.sqrt (dyadicGridLength A.G I.1))
    {Np : ℝ} (hNp : ∀ c d, (((D.paperToLeafQ qG).pe d).length * ((D.paperToLeafQ qG).pe c).length : ℝ) ≤ Np)
    (G₀ : bf.Grp)
    {Cy : ℝ} (hy : ∀ I ∈ S, ∀ l, (D.paperToLeafQ qG).u ≠ some l →
      ‖bf.basicIn fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy ∧
      ‖bf.Ucol fp.Mc l I‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Cy)
    {BU : ℝ} (hBU : ∑ I ∈ S, ∑ l, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU)
    (B : (D.paperToLeafQ qG).BallData gset) {ra rb : ℝ}
    (hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ' : ℝ} (hτ' : 0 < τ') (hτ1 : τ' ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ'⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτN : τ' * B.N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : ∀ l, Real.log (2 * ((D.paperToLeafQ qG).mbs l).B) ≤ kk ^ cc)
    (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hJc : (Jm : ℝ) ≤ cc * (Real.log kk + 1))
    (hLs : ∀ l, ((D.Lf.layers l).length : ℝ) ≤ cc * (Real.log kk + 1)) {Vl : Fin 4 → ℝ}
    (hlin : ∀ l, D.u ≠ some l → ∑ G ∈ gset, ∑ β ∈ Finset.range Bn, ‖(D.Ms l G).paperBlockSide
        (D.S.withQ0 (qG G))
        D.hA D.SP (A.R.1 + ((D.S.K * β : ℕ) : ℤ)) (fp.retainedV G (A.R.1 + ((D.S.K * β : ℕ) : ℤ))
          D.S.K) (D.c l G (A.R.1 + ((D.S.K * β : ℕ) : ℤ)))‖ ^ 2 ≤
        Vl l * dyadicGridLength A.G A.R.1)
    (hP : 1 ≤ fp.P) (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ)
    (hΓa : ∀ a, (D.paperToLeafQ qG).u ≠ some a → fp.stackEA (SideLeafM.nOs Lp Jm) ((D.paperToLeafQ qG).cat a)
        ((D.paperToLeafQ qG).mbs a) (D.paperToLeafQ qG).Dpre N (capV A cc kk)
      (sideB0 A cc kk (Vl a)) ≤
      (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1)
    (hΓb : ∀ b, (D.paperToLeafQ qG).u ≠ some b → (SideLeafM.nOs Lp Jm).card * (N * capV A cc kk +
        sideB0 A cc
        kk (Vl b)) ≤
      Γb b * dyadicGridLength A.G A.R.1)
    (hΓU : (SideLeafM.nOs Lp Jm).card * (2 * BU) ≤ ΓU * dyadicGridLength A.G A.R.1)
    {η p ρ : ℝ} (hη : 0 ≤ η) (hp : 2 / 3 < p) (hp1 : p ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : Finset (ℤ × ℤ), C ⊆ A.cells ∧
      dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 ∧
      ∑ I ∈ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2),
        dyadicGridLength A.G I.1 * min η ‖∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧
            (Finset.univ.filter fun l => σ l = 0).card = 2 ∧
            (Finset.univ.filter fun l => σ l = 1).card = 2),
          ∑ G ∈ gs I, fp.Λc I (fun l => if σ l = 0 then (D.paperToLeafQ qG).out l G I else
              (D.paperToLeafQ qG).sv l G
              I)‖ ≤
      6 * 256 * Np * (τ + cF) * (D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU
          (capV A cc
          kk) ρ *
          dyadicGridLength A.G A.R.1 +
        6 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4,
          (D.paperToLeafQ qG).nearBnd hq2 hq3 Nd N Lp Jm Mp C₀ (ρ / 64) Γa Γb ΓU a b e +
        η ^ (1 - p) * ((D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk)
            ρ ^
            (p / 2) *
          (D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2) *
          (D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2) *
          dyadicGridLength A.G A.R.1) ∧
      (∀ (core err : ℤ × ℤ → bf.Grp → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
        (S' : Finset (ℤ × ℤ)), S' ⊆ S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∀ {Bc : ℝ}, 0 ≤ Bc →
        (∀ I ∈ S', ∀ G ∈ gs I, ∀ l,
          ‖core I G l‖ ≤ Bc * Real.sqrt (dyadicGridLength A.G I.1)) →
        ∑ I ∈ S', dyadicGridLength A.G I.1 * min η (∑ σ ∈ Finset.univ.filter
          (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1),
            ‖∑ G ∈ gs I, fp.Λc I (patternPiece (core I G) (fun l => (D.paperToLeafQ qG).sv l G I) (err I
                G)
                σ)‖) ≤
        η ^ (1 - p) * (81 * localFormUniformConstant κ' *
          max Bc (Real.sqrt ((D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A
              cc kk)
              ρ))) ^ p *
          ((D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2) *
            (D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2)
                *
            (D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ ^ (p / 2)
                *
            dyadicGridLength A.G A.R.1)) ∧
      ∀ x, ∑ I ∈ (S.filter (fun I => ¬ ∃ e ∈ C,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
          (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ∑ G ∈ gs I, (D.paperToLeafQ qG).s2 G I ≤
        (D.paperToLeafQ qG).Tcap Lp Jm C₀ B₀ Cy (D.sideBs cc kk Vl BU) BU (capV A cc kk) ρ := by
  have hK := D.hK
  have hUle : ∀ l, ∑ I ∈ S, ‖bf.Ucol fp.Mc l I‖ ^ 2 ≤ BU := fun l =>
    (Finset.sum_le_sum fun I _ => Finset.single_le_sum (f := fun l' => ‖bf.Ucol fp.Mc l' I‖ ^ 2)
      (fun l' _ => sq_nonneg _) (Finset.mem_univ l)).trans hBU
  have hEU : ∀ l, (D.paperToLeafQ qG).u = some l → ∑ I ∈ S, ∑ G ∈ gs I,
      ‖columnL2Restriction (dyadicGridCell A.G I.1 I.2)
        (dyadicGridCell_measurable A.G I.1 I.2) ((D.paperToLeafQ qG).sv l G I)‖ ^ 2 ≤ 2 * BU := by
    intro l hl
    refine le_trans (Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun G _ =>
      columnL2Restriction_norm_sq_le _ _ _) ?_
    refine (D.paper_U_side_energy qG hl S hS gs gset hgs k hcertS B hroot' hτ' hτ1 hHed hτN).trans ?_
    linarith [hUle l]
  have hBs : ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2 ≤ D.sideBs cc kk Vl BU := by
    calc ∑ I ∈ S, ∑ G ∈ gs I, ∑ l, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2
        = ∑ I ∈ S, ∑ l, ∑ G ∈ gs I, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2 :=
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = ∑ l, ∑ I ∈ S, ∑ G ∈ gs I, ‖(D.paperToLeafQ qG).sv l G I‖ ^ 2 := Finset.sum_comm
      _ ≤ D.sideBs cc kk Vl BU := by
          unfold sideBs
          refine Finset.sum_le_sum fun l _ => ?_
          split_ifs with hl
          · refine (D.paper_U_side_energy qG hl S hS gs gset hgs k hcertS B hroot' hτ' hτ1 hHed
              hτN).trans ?_
            linarith [hUle l]
          · exact D.paper_basic_side_energy qG hanc hne hl S hS gs gset hgs k Bn hcertS hBn B hroot' hτ'
              hτ1 hHed hτN cc hc hk hDm hDb hLs (hlin l hl)
  exact (D.paperToLeafQ qG).leaf_side_estimateM hq2 hq3 hanc hne hKNd hKN S hS hroot gs gset hgs Lp Jm
      Bn k
    hBn hLp hJm Act hact hMp hcertS (fun _ G J => fp.Cert k G J) (fun _ => capV A cc kk)
    (fun l => sideB0 A cc kk (Vl l))
    (fun l _ => D.paper_toLeaf_cap qG hanc hne gset k B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hLs l)
    (fun l _ I hI G hG J _ hIJ => (hcertS I hI G hG).mono fp hIJ)
    (fun l hl => D.paper_block_energy qG hanc hne S hS gs gset k Bn hcertS hBn B hroot' hτ' hτ1 hHed hτN
      cc hc hk hDm hDb hLs (hlin l hl)) (EU := 2 * BU) hEU hτ hcF hC₀ hB₀ hpair hfar hbas hout
    hNp (Bs := D.sideBs cc kk Vl BU) hBs G₀ hy hBU B hroot' hτ' hτ1 hHed hτN cc hc hk hDm hDb hJc
    hP Γa Γb ΓU hΓa hΓb hΓU hη hp hp1 hρ hρ1

/-- The restored pattern in Section 9 has precisely the physical form of
    the two-side pattern used by the Section 7 stack estimate. The full
    augmented U side is retained only in the stack input. -/
open Classical in
theorem paper_restored_eq (qG : bf.Grp → ℕ)
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp)
    (hrep : ∀ l, D.u ≠ some l → (D.withQ0 (qG G)).RepAt L l G I)
    (σ : Fin 4 → Fin 3) :
    fp.Λc I (fun l => if σ l = 0 then
      (D.withQ0 (qG G)).paperCoreAt l G I + (D.withQ0 (qG G)).paperSideAt l G I +
      (D.withQ0 (qG G)).errAt L l G I else (D.withQ0 (qG G)).paperSideAt l G I) =
    fp.Λc I (fun l => if σ l = 0 then (D.paperToLeafQ qG).out l G I
      else (D.paperToLeafQ qG).sv l G I) := by
  rw [fp.Λc_phys, fp.Λc_phys I (fun l => if σ l = 0 then (D.paperToLeafQ qG).out l G I
    else (D.paperToLeafQ qG).sv l G I)]
  congr 1
  funext l
  have hs := D.paperToLeafQ_sv_physical qG l G I
  have hsfix : fp.physMain (bf.Lab ⊕ Fin fp.Mc) ((D.withQ0 (qG G)).paperSideAt l G I) =
      (D.withQ0 (qG G)).paperSideAt l G I := by
    rw [← hs, fp.physMain_physMain]
  split_ifs
  · have ho : (D.paperToLeafQ qG).out l G I = (D.withQ0 (qG G)).toLeaf.out l G I := rfl
    rw [ho, (D.withQ0 (qG G)).paper_phys_out_eq L hI l G (hrep l), map_add, map_add,
      (D.withQ0 (qG G)).paperCoreAt_physical, hsfix, (D.withQ0 (qG G)).physMain_errAt]
  · rw [hsfix, hs]

end SideInput
end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperGs_eq
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperGs_range
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeafQ_sv
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeafQ_out
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperGs_nat
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeaf_sv_basic
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeaf_sv_U
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_V_sum_le
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_basic_side_energy
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_block_energy
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_U_side_energy
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_toLeaf_cap
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_side_estimate
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeaf_sv_basic_exact
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeaf_sv_physical
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperToLeafQ_sv_physical

#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperCoreAt_physical
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_restored_eq
