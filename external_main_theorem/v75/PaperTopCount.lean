/-
Adapted from the pinned Joris Roos reference, TrilinearHT/Auto/
Sec13_5RepresentativesComponentSizesFirstTops.lean and
Sec13_4SideStatesFixedOffsets.lean. Copyright (c) 2026 Joris Roos;
original authors: Claude. Apache-2.0. See LICENSE-REFERENCE-APACHE2.
V75 replaces the reference side/core and logarithmic type predicates
consistently. Proof candidates; no Lean elaboration was performed.
-/
import ReferenceV75PaperFirstTops

set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace Auto
open MeasureTheory Metric OpenAI086.AdaptedV56 OpenAI086.ReferenceV70
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
theorem paper_tops_energy (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) (hanc : A.AncClosed)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k : ℕ)
    (hcol : ∀ G, (grp G).1 = k) (j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool)) (S : ModeSchedule) (hA : 6 ≤ S.A0) (SP : SideParams)
    {n : ℕ} (Ms : ι → ModeSystem A.G n) (q : ι → ℕ) (hq : ∀ G, 1 ≤ q G ∧ q G ≤ S.Q0) (L : ∀ G,
        LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms G).Md)
    (Bs : Finset ℤ) (c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ)
    (hcrep : ∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
      (Ms G).frozenEval (S.withQ0 (q G)) b J (c G b J) = columnL2Restriction (dyadicGridCell A.G
          J.1 J.2)
        (dyadicGridCell_measurable A.G J.1 J.2)
        ((L G).op (fp.frozenZ l s mb (grp G) j ls (b - 4 * S.K))))
    {Bc VE : ℝ}
    (hcB : ∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
      ∑ m ∈ (Ms G).alive (ancAt A.G J (b - 4 * S.K)), ‖c G b J m‖ ^ 2 ≤ Bc)
    (hVE : ∑ G, ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP b (fp.retainedV (grp G) b S.K)
        (c G b)‖ ^ 2 ≤
      VE)
    {Δ h : ℕ} (R : ∀ G, (Ms G).PaperRepClass (S.withQ0 (q G)) hA SP Δ h)
    (X : ∀ G, Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md))) (hX : ∀ G, (R G).Inst (X G))
    (hXr : ∀ G, ∀ p ∈ X G, p.2.1 ∈ Bs ∧ p.2.2.1 ∈ fp.retainedV (grp G) p.2.1 S.K)
    (hD : 2 ≤ S.Dstar) (hδ : ∀ G, 0 < (Ms G).δc) (hΛ : ∀ G, (Ms G).Λ ≤ S.Dstar)
    (_hQ0 : 0 < S.Q0) (Kf : ℕ) (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : ∀ G, gaugeSqNorm (Ms G).zc.dim (Ms G).δc ≤ S.Dstar)
    (hKf : ∀ G, 2 * gaugeTail (Ms G).zc.dim (Ms G).δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ G m, S.Dstar⁻¹ ≤ (Ms G).L.εM m)
    (halive : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).card : ℝ) ≤ S.Dstar)
    (hpt : ∀ G y, (((Ms G).ptSet y).card : ℝ) ≤ S.Dstar)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHτ : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {Nq : ℕ} (hNq : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ Nq)
    (hτN : τ * Nq * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hcc : 1 ≤ cc) {kq : ℝ} (hkq : 1 ≤ kq)
    (hDmq : Real.log (2 * mb.B) ≤ kq ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kq ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kq + 1))
    {σ₀ : ℝ} (hab : 6 * Bc / S.Dstar ^ 59 ≤ σ₀) :
    σ₀ * ∑ G, ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G)
        h) σ₀,
        dyadicGridLength A.G p.1.1 ≤
      24 * (2 * Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
          (1 + Real.log (2 * kq)) ^ 2) * dyadicGridLength A.G A.R.1 + 2 * S.K * VE) := by
  have hK0 : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hR0 : 0 < dyadicGridLength A.G A.R.1 := dyadicGridLength_pos A.G A.R.1
  -- the span projections of the rows
  have inst : ∀ G (e : (Ms G).Event),
      (Submodule.span ℂ (((Ms G).evMode e) '' (e.2.2 : Set (Ms G).Md))).HasOrthogonalProjection :=
    fun G e => by
      have : FiniteDimensional ℂ
          (Submodule.span ℂ (((Ms G).evMode e) '' (e.2.2 : Set (Ms G).Md))) :=
        FiniteDimensional.span_of_finite ℂ (e.2.2.finite_toSet.image _)
      infer_instance
  -- the decision cells of the tops
  have hdec : ∀ G, ∀ p ∈ X G, A.R.1 ≤ p.2.1 - 4 * S.K →
      ancAt A.G p.1 (p.2.1 - 4 * S.K) ∈ A.cells ∧
        dyadicGridCell A.G p.1.1 p.1.2 ⊆ dyadicGridCell A.G (ancAt A.G p.1 (p.2.1 - 4 * S.K)).1
          (ancAt A.G p.1 (p.2.1 - 4 * S.K)).2 ∧
        fp.Cert k (grp G) (ancAt A.G p.1 (p.2.1 - 4 * S.K)) := by
    intro G p hp hR
    obtain ⟨hcN, hIJ, -, -⟩ := hX G p hp
    obtain ⟨-, hJr⟩ := hXr G p hp
    obtain ⟨hJU, hUc, hcert⟩ := fp.retained_decision hanc hJr hR
    have he : ancAt A.G p.1 (p.2.1 - 4 * S.K) = ancAt A.G p.2.2.1 (p.2.1 - 4 * S.K) :=
      ancAt_eq_ancAt_of_subset hIJ
          (by rw [(R G).hNd _ hcN]; simp only [ModeSchedule.withQ0_K]; omega)
    rw [he]
    refine ⟨hUc, hIJ.trans hJU, ?_⟩
    rw [← hcol G]; exact hcert
  -- absorption on each group
  have habs : ∀ G, σ₀ * ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA
      SP (c G) h) σ₀,
      dyadicGridLength A.G p.1.1 ≤
      24 * (∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h)
          σ₀,
          ‖(Submodule.span ℂ (((Ms G).evMode ((Ms G).topRow (S.withQ0 (q G)) hA h p)) ''
            (((Ms G).topRow (S.withQ0 (q G)) hA h p).2.2 : Set (Ms G).Md))).starProjection
            ((Ms G).frozenEval (S.withQ0 (q G)) p.2.1 p.2.2.1 (c G p.2.1 p.2.2.1))‖ ^ 2 +
        ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h) σ₀,
          ‖∑ m ∈ ((Ms G).nodeComp (S.withQ0 (q G)) hA h p.2).filter
            (fun m => ¬ (Ms G).paperIsCoreAt (S.withQ0 (q G)) hA SP p.2.1 p.2.2.1 m),
            c G p.2.1 p.2.2.1 m • (Ms G).cellMode p.1 m‖ ^ 2) := fun G =>
    (R G).tops_absorb (hX G) (c G) hD (hδ G) (hΛ G) (lt_of_lt_of_le zero_lt_one (hq G).1) Kf
      (ModeSchedule.withQ0_box (hq G).2 (by positivity) hbox) (hDg G) (hKf G) (hεw G)
      (fun p _ => halive G _) (fun p hp => hcB G p.2.1 (hXr G p hp).1 p.2.2.1 (hXr G p hp).2) hab
      (inst := inst G)
  -- the side part (`PaperRepClass.tops_side` and `eq:linear-energy`)
  have hside : ∀ G, ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
      (c G) h) σ₀,
      ‖∑ m ∈ ((Ms G).nodeComp (S.withQ0 (q G)) hA h p.2).filter
        (fun m => ¬ (Ms G).paperIsCoreAt (S.withQ0 (q G)) hA SP p.2.1 p.2.2.1 m),
        c G p.2.1 p.2.2.1 m • (Ms G).cellMode p.1 m‖ ^ 2 ≤
      2 * S.K * ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP b (fp.retainedV (grp G) b S.K)
          (c G b)‖ ^ 2 :=
    fun G => (R G).tops_side (hX G) _ σ₀ (fun b => fp.retainedV (grp G) b S.K)
      (fun b J hJ => ((fp.mem_retainedV).mp hJ).2.1) (fun p hp => (hXr G p hp).2) Bs
      (fun p hp => (hXr G p hp).1) (c G) hD (hδ G) (hΛ G) (lt_of_lt_of_le zero_lt_one (hq G).1) Kf
      (ModeSchedule.withQ0_box (hq G).2 (by positivity) hbox) (hDg G) (hKf G) (hεw G)
      (fun b J _ => halive G _)
  -- the row outputs: the blocks before the attempt root contribute nothing
  have hPZ : ∀ G, ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
      (c G) h) σ₀,
      ‖(Submodule.span ℂ (((Ms G).evMode ((Ms G).topRow (S.withQ0 (q G)) hA h p)) ''
        (((Ms G).topRow (S.withQ0 (q G)) hA h p).2.2 : Set (Ms G).Md))).starProjection
        ((Ms G).frozenEval (S.withQ0 (q G)) p.2.1 p.2.2.1 (c G p.2.1 p.2.2.1))‖ ^ 2 =
      ∑ e ∈ (((Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h)
          σ₀).filter
          (fun p => A.R.1 ≤ p.2.1 - 4 * S.K)).image ((Ms G).topRow (S.withQ0 (q G)) hA h),
        ‖(Submodule.span ℂ (((Ms G).evMode e) '' (e.2.2 : Set (Ms G).Md))).starProjection
          ((L G).op (fp.basicOut l s mb (grp G) j ls
            (ancAt A.G e.2.1 (e.1 - 4 * S.K)).1))‖ ^ 2 := by
    intro G
    have hinj : Set.InjOn ((Ms G).topRow (S.withQ0 (q G)) hA h)
        ((((Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h)
            σ₀).filter
          (fun p => A.R.1 ≤ p.2.1 - 4 * S.K) : Finset _) : Set _) :=
      ((R G).topRow_injOn (hX G) _ σ₀).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    rw [Finset.sum_image hinj, ← Finset.sum_filter_add_sum_filter_not _
      (fun p => A.R.1 ≤ p.2.1 - 4 * S.K)]
    have hzero : ∑ p ∈ ((Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
        (c G) h)
        σ₀).filter (fun p => ¬ A.R.1 ≤ p.2.1 - 4 * S.K),
        ‖(Submodule.span ℂ (((Ms G).evMode ((Ms G).topRow (S.withQ0 (q G)) hA h p)) ''
          (((Ms G).topRow (S.withQ0 (q G)) hA h p).2.2 : Set (Ms G).Md))).starProjection
          ((Ms G).frozenEval (S.withQ0 (q G)) p.2.1 p.2.2.1 (c G p.2.1 p.2.2.1))‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨hpT, hR⟩ := Finset.mem_filter.mp hp
      have hpX : p ∈ X G := (Finset.mem_filter.mp hpT).1
      have hfz : fp.frozenZ l s mb (grp G) j ls (p.2.1 - 4 * S.K) = 0 := by
        simp [frozenZ, not_le.mp hR]
      rw [hcrep G p.2.1 (hXr G p hpX).1 p.2.2.1 (hXr G p hpX).2, hfz, map_zero, map_zero,
        map_zero, norm_zero]
      norm_num
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpT, hR⟩ := Finset.mem_filter.mp hp
    have hpX : p ∈ X G := (Finset.mem_filter.mp hpT).1
    obtain ⟨hcN, hIJ, -, -⟩ := hX G p hpX
    rw [hcrep G p.2.1 (hXr G p hpX).1 p.2.2.1 (hXr G p hpX).2]
    have hz : fp.frozenZ l s mb (grp G) j ls (p.2.1 - 4 * S.K) =
        fp.basicOut l s mb (grp G) j ls (ancAt A.G p.1 (p.2.1 - 4 * S.K)).1 := by
      simp [frozenZ, not_lt.mpr hR, ancAt]
    rw [hz]
    exact congrArg (fun x => ‖x‖ ^ 2) ((Ms G).evProj_restrict ((Ms G).topRow (S.withQ0 (q G)) hA h
        p)
      (dyadicGridCell_measurable A.G p.2.2.1.1 p.2.2.1.2) hIJ _)
  -- lem:lift-composition on the rows of the tops
  have hrows := fp.lift_composition_dep l s hT htag d mb hne (ρ := fun G => (Ms G).Event) grp hgrp
    k j hPH ls (fun G => (Ms G).Md) L (fun G => ColumnL2 (Ms G).Md)
    (fun G => (((Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h)
        σ₀).filter
      (fun p => A.R.1 ≤ p.2.1 - 4 * S.K)).image ((Ms G).topRow (S.withQ0 (q G)) hA h))
    (fun G e => (Submodule.span ℂ (((Ms G).evMode e) '' (e.2.2 : Set (Ms G).Md))).starProjection)
    (c := 2) (by norm_num) (fun G x => ?_) (fun G e => ancAt A.G e.2.1 (e.1 - 4 * S.K))
    (fun G e he => ?_) (fun G e he => ?_) (fun G e he => ?_) hroot hτ hτ1 hHτ (N := Nq) ?_
  rotate_left
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image
      (Finset.filter_subset _ _)) fun _ _ _ => sq_nonneg _).trans
      ((R G).firstTops_rows (hX G) _ σ₀ hD (hδ G) (hΛ G) (lt_of_lt_of_le zero_lt_one (hq G).1) Kf
      (ModeSchedule.withQ0_box (hq G).2 (by positivity) hbox) (hDg G) (hKf G) (hεw G)
        (hpt G) (inst := inst G) x)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hpT, hR⟩ := Finset.mem_filter.mp hp
    exact (hdec G p (Finset.mem_filter.mp hpT).1 hR).1
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hpT, hR⟩ := Finset.mem_filter.mp hp
    exact ContinuousLinearMap.ext fun w => (Ms G).evProj_restrict ((Ms G).topRow (S.withQ0 (q G))
        hA h p) _
      (hdec G p (Finset.mem_filter.mp hpT).1 hR).2.1 w
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hpT, hR⟩ := Finset.mem_filter.mp hp
    exact (hdec G p (Finset.mem_filter.mp hpT).1 hR).2.2
  · convert hNq using 0
  have hG0 := fp.liftConst_le_G0 l s mb ls (c := 2) (by norm_num) hτ hτN cc hcc hkq hDmq hDb hn
  -- combine
  set G0 := Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
    (1 + Real.log (2 * kq)) ^ 2)
  have hPZsum : ∑ G, ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
      (c G) h) σ₀,
      ‖(Submodule.span ℂ (((Ms G).evMode ((Ms G).topRow (S.withQ0 (q G)) hA h p)) ''
        (((Ms G).topRow (S.withQ0 (q G)) hA h p).2.2 : Set (Ms G).Md))).starProjection
        ((Ms G).frozenEval (S.withQ0 (q G)) p.2.1 p.2.2.1 (c G p.2.1 p.2.2.1))‖ ^ 2 ≤
      2 * G0 * dyadicGridLength A.G A.R.1 := by
    rw [Finset.sum_congr rfl fun G _ => hPZ G]
    exact hrows.trans (mul_le_mul_of_nonneg_right hG0 hR0.le)
  have hVsum : ∑ G, ∑ p ∈ (Ms G).firstTops (X G) (R G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
      (c G) h) σ₀,
      ‖∑ m ∈ ((Ms G).nodeComp (S.withQ0 (q G)) hA h p.2).filter
        (fun m => ¬ (Ms G).paperIsCoreAt (S.withQ0 (q G)) hA SP p.2.1 p.2.2.1 m),
        c G p.2.1 p.2.2.1 m • (Ms G).cellMode p.1 m‖ ^ 2 ≤ 2 * S.K * VE := by
    refine (Finset.sum_le_sum fun G _ => hside G).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hVE (by positivity)
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun G _ => habs G).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (add_le_add hPZsum hVsum) (by norm_num)

open Classical in
theorem paper_first_top_count (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) (hanc : A.AncClosed)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k : ℕ)
    (hcol : ∀ G, (grp G).1 = k) (j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool)) (S : ModeSchedule) (hA : 6 ≤ S.A0) (SP : SideParams)
    {n : ℕ} (Ms : ι → ModeSystem A.G n) (q : ι → ℕ) (hq : ∀ G, 1 ≤ q G ∧ q G ≤ S.Q0) (L : ∀ G,
        LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms G).Md)
    (Bs : Finset ℤ) (c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ)
    (hcrep : ∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
      (Ms G).frozenEval (S.withQ0 (q G)) b J (c G b J) = columnL2Restriction (dyadicGridCell A.G
          J.1 J.2)
        (dyadicGridCell_measurable A.G J.1 J.2)
        ((L G).op (fp.frozenZ l s mb (grp G) j ls (b - 4 * S.K))))
    {Bc V₀ : ℝ}
    (hcB : ∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
      ∑ m ∈ (Ms G).alive (ancAt A.G J (b - 4 * S.K)), ‖c G b J m‖ ^ 2 ≤ Bc)
    (hVE : ∑ G, ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP b (fp.retainedV (grp G) b S.K)
        (c G b)‖ ^ 2 ≤
      V₀ * dyadicGridLength A.G A.R.1)
    (Hs : Finset ℕ) (Ts : Finset (ℕ × ℕ)) (Thr : Finset ℝ) (hThr : ∀ σ ∈ Thr, S.Dstar⁻¹ ≤ σ)
    (hCH : (Hs ×ˢ Ts ×ˢ Thr).Nonempty)
    {Δ : ℕ} (R : ∀ (h : ℕ) (_ : ℕ × ℕ) G, (Ms G).PaperRepClass (S.withQ0 (q G)) hA SP Δ h)
    (X : ∀ (_ : ℕ) (_ : ℕ × ℕ) G, Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md)))
    (hX : ∀ h τ G, (R h τ G).Inst (X h τ G))
    (hXr : ∀ h τ G, ∀ p ∈ X h τ G, p.2.1 ∈ Bs ∧ p.2.2.1 ∈ fp.retainedV (grp G) p.2.1 S.K)
    (hD : 2 ≤ S.Dstar) (hδ : ∀ G, 0 < (Ms G).δc) (hΛ : ∀ G, (Ms G).Λ ≤ S.Dstar)
    (hQ0 : 0 < S.Q0) (Kf : ℕ) (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : ∀ G, gaugeSqNorm (Ms G).zc.dim (Ms G).δc ≤ S.Dstar)
    (hKf : ∀ G, 2 * gaugeTail (Ms G).zc.dim (Ms G).δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ G m, S.Dstar⁻¹ ≤ (Ms G).L.εM m)
    (halive : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).card : ℝ) ≤ S.Dstar)
    (hpath : ∀ y, (∑ G, ((Ms G).ptSet y).card : ℝ) ≤ S.Dstar)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHτ : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {Nq : ℕ} (hNq : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ Nq)
    (hτN : τ * Nq * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hcc : 1 ≤ cc) {kq : ℝ} (hkq : 1 ≤ kq)
    (hDmq : Real.log (2 * mb.B) ≤ kq ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kq ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kq + 1))
    (hab : 6 * Bc / S.Dstar ^ 59 ≤ S.Dstar⁻¹ ^ 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ Cut : Finset (ℤ × ℤ), dyadicRootLength A.G Cut ≤ ρ * dyadicGridLength A.G A.R.1 ∧
      ∀ y : ℝ, ∀ h ∈ Hs, ∀ t ∈ Ts, ∀ σ ∈ Thr,
        (∑ G, (((X h t G).filter fun p => (∀ e ∈ Cut, ¬ dyadicGridCell A.G p.1.1 p.1.2 ⊆
            dyadicGridCell A.G e.1 e.2) ∧ y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
            σ ^ 2 ≤ (Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h p).image
              (fun p => (R h t G).rep p.2)).card : ℝ) ≤
          min S.Dstar (24 * (2 * Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
            (1 + Real.log (2 * kq)) ^ 2) + 2 * S.K * V₀) * (Hs ×ˢ Ts ×ˢ Thr).card /
              (ρ * σ ^ 2)) := by
  have hDp : 0 < S.Dstar := by linarith
  have hR0 : 0 < dyadicGridLength A.G A.R.1 := dyadicGridLength_pos A.G A.R.1
  set G0 := Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
    (1 + Real.log (2 * kq)) ^ 2) with hG0
  set M := 24 * (2 * G0 + 2 * S.K * V₀) with hM
  -- the tops of a choice, over all groups
  set! Tch : ℕ × (ℕ × ℕ) × ℝ → Finset (Σ G, (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md)) := fun ch =>
    Finset.univ.sigma fun G => (Ms G).firstTops (X ch.1 ch.2.1 G) (R ch.1 ch.2.1 G).rep
      ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) ch.1) (ch.2.2 ^ 2) with hTch
  set! cellOf : (Σ G, (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md)) → ℤ × ℤ := fun t => t.2.1 with hcellOf
  set! Sc := (Hs ×ˢ Ts ×ˢ Thr).biUnion fun ch => (Tch ch).image cellOf with hSc
  -- the mass of the tops of each choice
  have hpt : ∀ G y, (((Ms G).ptSet y).card : ℝ) ≤ S.Dstar := fun G y =>
    (Finset.single_le_sum (f := fun G => (((Ms G).ptSet y).card : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ G)).trans (hpath y)
  have hmass : ∀ ch ∈ Hs ×ˢ Ts ×ˢ Thr, ∑ t ∈ Tch ch, dyadicGridLength A.G (cellOf t).1 ≤
      M / ch.2.2 ^ 2 * dyadicGridLength A.G A.R.1 := by
    intro ch hch
    have hσ : ch.2.2 ∈ Thr := (Finset.mem_product.mp (Finset.mem_product.mp hch).2).2
    have hσpos : 0 < ch.2.2 := lt_of_lt_of_le (inv_pos.mpr hDp) (hThr _ hσ)
    have hab' : 6 * Bc / S.Dstar ^ 59 ≤ ch.2.2 ^ 2 :=
      hab.trans (pow_le_pow_left₀ (inv_pos.mpr hDp).le (hThr _ hσ) 2)
    have hE := fp.paper_tops_energy l s hT htag d mb hne hanc grp hgrp k hcol j hPH ls S hA SP Ms q hq L
        Bs c
      hcrep hcB hVE (R := R ch.1 ch.2.1) (X ch.1 ch.2.1) (hX ch.1 ch.2.1) (hXr ch.1 ch.2.1) hD hδ
      hΛ hQ0 Kf hbox hDg hKf hεw halive hpt hroot hτ hτ1 hHτ hNq hτN cc hcc hkq hDmq hDb hn hab'
    have hsum : ∑ t ∈ Tch ch, dyadicGridLength A.G (cellOf t).1 =
        ∑ G, ∑ p ∈ (Ms G).firstTops (X ch.1 ch.2.1 G) (R ch.1 ch.2.1 G).rep
          ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) ch.1) (ch.2.2 ^ 2), dyadicGridLength A.G
              p.1.1 := by
      simp only [hTch, hcellOf]
      rw [Finset.sum_sigma]
    rw [hsum, div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
    refine hE.trans (le_of_eq ?_)
    simp only [hM, hG0]
    ring
  -- all top cells lie in the root
  have hrootR : ∀ e ∈ Sc, dyadicGridCell A.G e.1 e.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 := by
    intro e he
    obtain ⟨ch, -, het⟩ := Finset.mem_biUnion.mp he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp het
    obtain ⟨G, p⟩ := t
    have hp := (Finset.mem_sigma.mp ht).2
    have hpX := (Finset.mem_filter.mp hp).1
    obtain ⟨-, hIJ, -, -⟩ := hX _ _ G p hpX
    obtain ⟨-, hJr⟩ := hXr _ _ G p hpX
    exact hIJ.trans ((dyadicFiniteTree_mem_iff A.G A.R _ _).mp ((fp.mem_retainedV).mp hJr).1).1
  obtain ⟨Cut, hcost, hcount⟩ := tops_cut_many A.G Sc (Hs ×ˢ Ts ×ˢ Thr) Tch cellOf
    (fun ch hch t ht => Finset.mem_biUnion.mpr ⟨ch, hch, Finset.mem_image_of_mem _ ht⟩) A.R
    hrootR hρ hρ1 hCH hmass
  refine ⟨Cut, hcost, fun y h hh t ht σ hσ => le_min ?_ ?_⟩
  · -- the full mode budget along the path
    refine le_trans ?_ (hpath y)
    refine Finset.sum_le_sum fun G _ => Nat.cast_le.mpr (Finset.card_le_card fun a ha => ?_)
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hpX, -, hy', -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hcN, hIJ, -, -⟩ := hX h t G p hpX
    have hal := (Ms G).mem_alive_of_mem_predOfMode (S.withQ0 (q G)) hA Δ h ((R h t G).halive _ hcN)
      ((R h t G).hrep p.2)
    have hJU := subset_ancAt A.G p.2.2.1 (show p.2.1 - 4 * S.K ≤ p.2.2.1.1 by
      rw [(R h t G).hNd _ hcN]; simp only [ModeSchedule.withQ0_K]
      have := (Nat.cast_nonneg S.K : (0 : ℤ) ≤ S.K); omega)
    exact ((Ms G).mem_ptSet).mpr ((Ms G).mem_alive.mp hal (hJU (hIJ hy')))
  · -- the retained first tops
    have hch : (h, t, σ) ∈ Hs ×ˢ Ts ×ˢ Thr :=
      Finset.mem_product.mpr ⟨hh, Finset.mem_product.mpr ⟨ht, hσ⟩⟩
    have hσpos : 0 < σ := lt_of_lt_of_le (inv_pos.mpr hDp) (hThr _ hσ)
    have hc := hcount y (h, t, σ) hch
    have hsig : (((Tch (h, t, σ)).filter fun t' => (∀ d ∈ Cut,
        ¬ dyadicGridCell A.G (cellOf t').1 (cellOf t').2 ⊆ dyadicGridCell A.G d.1 d.2) ∧
          y ∈ dyadicGridCell A.G (cellOf t').1 (cellOf t').2).card : ℝ) =
        ∑ G, ((((Ms G).firstTops (X h t G) (R h t G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
            (c G) h)
          (σ ^ 2)).filter fun q => (∀ d ∈ Cut, ¬ dyadicGridCell A.G q.1.1 q.1.2 ⊆
            dyadicGridCell A.G d.1 d.2) ∧ y ∈ dyadicGridCell A.G q.1.1 q.1.2).card : ℝ) := by
      simp only [hTch, hcellOf, Finset.card_filter]
      rw [Finset.sum_sigma]
      push_cast
      refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> rfl
    rw [hsig] at hc
    have hG : ∀ G, ((((X h t G).filter fun p => (∀ e ∈ Cut, ¬ dyadicGridCell A.G p.1.1 p.1.2 ⊆
        dyadicGridCell A.G e.1 e.2) ∧ y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
          σ ^ 2 ≤ (Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h p).image
            (fun p => (R h t G).rep p.2)).card : ℝ) ≤
        ((((Ms G).firstTops (X h t G) (R h t G).rep ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP
          (c G) h) (σ ^ 2)).filter fun q => (∀ d ∈ Cut, ¬ dyadicGridCell A.G q.1.1 q.1.2 ⊆
            dyadicGridCell A.G d.1 d.2) ∧ y ∈ dyadicGridCell A.G q.1.1 q.1.2).card : ℝ) := by
      intro G
      have hP : ∀ I J : ℤ × ℤ, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 →
          (∀ e ∈ Cut, ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) →
            ∀ e ∈ Cut, ¬ dyadicGridCell A.G J.1 J.2 ⊆ dyadicGridCell A.G e.1 e.2 :=
        fun I J hIJ hI e he hJe => hI e he (hIJ.trans hJe)
      exact Nat.cast_le.mpr ((Ms G).card_reps_le_firstTops_of (X h t G) (R h t G).rep
        ((Ms G).paperNodeSize (S.withQ0 (q G)) hA SP (c G) h) (σ ^ 2) y
        (fun I => ∀ e ∈ Cut, ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) hP)
    refine le_trans (Finset.sum_le_sum fun G _ => hG G) ?_
    refine hc.trans (le_of_eq ?_)
    field_simp

open Classical in
theorem paper_first_top_count_main (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) (hanc : A.AncClosed)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k : ℕ)
    (hcol : ∀ G, (grp G).1 = k) {j : ℕ} (hj : j ≤ 4) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool))
    (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : S.Valid Cj CA CT CK δs W)
    (hA : 6 ≤ S.A0) (hCj : 340 ≤ Cj) (hCA : 5 ≤ CA) (hCT : 4 ≤ CT) (hδs : 0 < δs)
    (hδ1 : δs ≤ 1) (hd2 : 2 ≤ S.dmax)
    (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (hQ : 1 ≤ S.Q0) (hDm : 2 ≤ S.Dm)
    (hW : 8 * ((S.dmax : ℝ) + 1) ^ 3 * Real.log (2 * S.H) / Real.log 2 ≤ W)
    (D dB : ℕ) {H δc N kk : ℝ} (hHed : 2 ≤ fp.Hed) (hH : 1 ≤ H) (hδc : 0 < δc) (hN0 : 0 ≤ N)
    (hNl : ∀ I ∈ A.cells,
      ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N)
    {n : ℕ} (Ms : ι → ModeSystem A.G n) (q : ι → ℕ) (hq : ∀ G, 1 ≤ q G ∧ q G ≤ S.Q0) (L : ∀ G,
        LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms G).Md)
    (gs : ι → ℤ)
    (hex : ∀ G, fp.MainLiftExports l s (grp G) j d D dB H (gs G) (L G) (Ms G).wave (Ms G).cellOf)
    (hεM : ∀ G m, (L G).εM m = (Ms G).L.εM m)
    (hdim : ∀ G p, (Ms G).dvOf p + (Ms G).zc.dim ≤ S.dmax) {M : ℕ} (hM1 : 1 ≤ M)
    (hMD : (M : ℝ) ≤ 2 * S.Dm)
    (hM : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).image (Ms G).keyOf).card ≤ M)
    (hδ : ∀ G, 0 < (Ms G).δc) (hΛ : ∀ G, (Ms G).Λ ≤ S.Dstar) (Kf : ℕ)
    (hDg : ∀ G, gaugeSqNorm (Ms G).zc.dim (Ms G).δc ≤ S.Dstar)
    (hKf : ∀ G, 2 * gaugeTail (Ms G).zc.dim (Ms G).δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hBox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Bstar) (hεw : ∀ G m, S.Dstar⁻¹ ≤ (Ms G).L.εM m)
    (halive : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).card : ℝ) ≤ S.Dstar)
    (hpath : ∀ y, (∑ G, ((Ms G).ptSet y).card : ℝ) ≤ S.Dstar)
    (hBσ : ∀ G, 2 * (S.Q0 * (3 * ((Ms G).Bσ * (Ms G).Bσ) ^ 2)) ^ 2 ≤ (⌊S.Dstar⌋₊ : ℝ))
    (hstar : fp.modeStar D dB H δc N kk ≤ S.Dstar)
    {CF : ℝ} (hCF : 0 ≤ CF) (hCFD : 24 * CF ≤ S.Dstar ^ 55)
    (hnorm : ∀ jb : Fin 2, ∀ U ∈ A.cells, ‖columnL2Restriction (dyadicGridCell A.G U.1 U.2)
      (dyadicGridCell_measurable A.G U.1 U.2) (bf.P l jb).Z‖ ^ 2 ≤ CF * dyadicGridLength A.G U.1)
    (R₀ : ℤ) (Bs : Finset ℤ) (hgrid : ∀ b ∈ Bs, (S.K : ℤ) ∣ b - R₀)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHτ : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {Nq : ℕ} (hNq : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ Nq)
    (hτN : τ * Nq * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hcc : 1 ≤ cc) {kq : ℝ} (hkq : 1 ≤ kq)
    (hDmq : Real.log (2 * mb.B) ≤ kq ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kq ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kq + 1))
    (Ts : Finset (ℕ × ℕ)) (Thr : Finset ℝ) (hThr : ∀ σ ∈ Thr, S.Dstar⁻¹ ≤ σ)
    (hTs : Ts.Nonempty) (hThr0 : Thr.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ,
      (∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
        (Ms G).frozenEval (S.withQ0 (q G)) b J (c G b J) = columnL2Restriction (dyadicGridCell A.G
            J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)
          ((L G).op (fp.frozenZ l s mb (grp G) j ls (b - 4 * S.K)))) ∧
      (∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
        ∑ m ∈ (Ms G).alive (ancAt A.G J (b - 4 * S.K)), ‖c G b J m‖ ^ 2 ≤ 4 * S.Dstar ^ 2 * CF) ∧
      ∑ G, ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA (S.sideParams δs) b
          (fp.retainedV (grp G) b S.K) (c G b)‖ ^ 2 ≤
        24 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1) *
          (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
              (1 + Real.log (2 * kq)) ^ 2) + 2 * CF / S.Dstar ^ 394) *
          dyadicGridLength A.G A.R.1 ∧
      ∃ R : ∀ (h : ℕ) (_ : ℕ × ℕ) G, (Ms G).PaperRepClass (S.withQ0 (q G)) hA (S.sideParams δs) 10 h,
        (∀ h ≤ S.Jstar, ∀ t G, (R h t G).Nd = ((Ms G).paperSuccNodes (S.withQ0 (q G)) hA
            (S.sideParams δs)
          (fp.retainedPairs (grp G) Bs S.K) h).filter
            (fun c => (Ms G).paperNodeType1 (S.withQ0 (q G)) hA 10 h c = t.1 ∧ (Ms G).paperNodeType2
                (S.withQ0 (q G)) hA 10 h c = t.2)) ∧
        ∃ Cut : Finset (ℤ × ℤ), dyadicRootLength A.G Cut ≤ ρ * dyadicGridLength A.G A.R.1 ∧
          ∀ y : ℝ, ∀ h ∈ Finset.range (S.Jstar + 1), ∀ t ∈ Ts, ∀ σ ∈ Thr,
              (∑ G, (((fp.useInst (grp G) S.K (R h t G).Nd).filter fun p =>
                  (∀ e ∈ Cut, ¬ dyadicGridCell A.G p.1.1 p.1.2 ⊆ dyadicGridCell A.G e.1 e.2) ∧
                  y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
                    σ ^ 2 ≤ (Ms G).paperNodeSize (S.withQ0 (q G)) hA (S.sideParams δs) (c G) h p).image
                    (fun p => (R h t G).rep p.2)).card : ℝ) ≤
                min S.Dstar (24 * (2 * Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) +
                  4) * (1 + Real.log (2 * kq)) ^ 2) + 2 * S.K * (24 *
                    (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1) *
                    (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
                      (1 + Real.log (2 * kq)) ^ 2) + 2 * CF / S.Dstar ^ 394))) *
                  (Finset.range (S.Jstar + 1) ×ˢ Ts ×ˢ Thr).card / (ρ * σ ^ 2)) := by
  have hK0 : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hDp : 0 < S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ S.Dstar := by linarith
  -- the frozen coefficients and the linear-side energy (`eq:linear-energy`)
  obtain ⟨c, hcrep, hcB, hVE⟩ := fp.paper_linear_energy l s hT htag d mb hne hanc grp hgrp k hcol hj
    hPH ls S hV hCj (le_trans (by norm_num) hCA) hδs hδ1 hd2 hD hB hQ hDm hW D dB hHed hH hδc hN0
    hNl Ms q hq L gs hex hεM hdim hM1 hMD hM hδ hΛ Kf hDg hKf hBox hεw halive hpath hstar hCF hnorm
        R₀
    Bs hgrid hroot hτ hτ1 hHτ hNq hτN cc hcc hkq hDmq hDb hn
  refine ⟨c, hcrep, hcB, hVE, ?_⟩
  -- the box of shifts at height zero
  have hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0 := by
    have hBA : S.Bstar ≤ S.A0 := by
      have hb := hV.base_le_A0 (le_trans (by norm_num) hCA) hd2 hD hB
      have hC := hV.two_le_Cstar hd2 hD
      have h6 : (1 : ℝ) ≤ 6 ^ S.Rht := one_le_pow₀ (by norm_num)
      have h1 : 1 ≤ S.Cstar * 6 ^ S.Rht := one_le_mul_of_one_le_of_one_le (by linarith) h6
      have h2 : S.Bstar ≤ S.Cstar * 6 ^ S.Rht * S.Bstar :=
        le_mul_of_one_le_left (by linarith) h1
      have h3 : S.Cstar * 6 ^ S.Rht * S.Bstar ≤ S.Cstar * 6 ^ S.Rht * S.Bstar * S.Dstar :=
        le_mul_of_one_le_right (by positivity) hD1
      linarith
    have hE0 : S.Eh 0 = S.A0 := by unfold ModeSchedule.Eh; ring
    rw [hE0]; linarith
  have hQ0 : 0 < S.Q0 := by omega
  -- the representative classes of the successful nodes
  have hRex : ∀ (h : ℕ) (t : ℕ × ℕ) G, ∃ R : (Ms G).PaperRepClass (S.withQ0 (q G)) hA (S.sideParams δs)
      10 h,
      (h ≤ S.Jstar → R.Nd = ((Ms G).paperSuccNodes (S.withQ0 (q G)) hA (S.sideParams δs)
        (fp.retainedPairs (grp G) Bs S.K) h).filter
          (fun c => (Ms G).paperNodeType1 (S.withQ0 (q G)) hA 10 h c = t.1 ∧ (Ms G).paperNodeType2 (S.withQ0
              (q G)) hA 10 h c = t.2)) ∧
      (¬ h ≤ S.Jstar → R.Nd = ∅) := by
    intro h t G
    by_cases hh : h ≤ S.Jstar
    · have hP : ∀ bJ ∈ fp.retainedPairs (grp G) Bs S.K, bJ.2.1 = bJ.1 - 2 * S.K := fun bJ hbJ =>
        ((fp.mem_retainedV).mp ((fp.mem_retainedPairs).mp hbJ).2).2.1
      obtain ⟨hal, hNd, hgood, hdist⟩ := (Ms G).paperSuccNodes_props (S.withQ0 (q G)) hA
          (S.sideParams δs)
        (fp.retainedPairs (grp G) Bs S.K) hP h
      have hblk : ∀ c ∈ (Ms G).paperSuccNodes (S.withQ0 (q G)) hA (S.sideParams δs)
          (fp.retainedPairs (grp G) Bs S.K) h, (S.K : ℤ) ∣ c.1 - R₀ := by
        intro c hc
        obtain ⟨bJ, hbJ, x, -, rfl⟩ := ((Ms G).mem_paperSuccNodes (S.withQ0 (q G)) hA).mp hc
        exact hgrid _ ((fp.mem_retainedPairs).mp hbJ).1
      obtain ⟨R, hR⟩ := (Ms G).exists_paperRepClass (S.withQ0 (q G)) hA (hV.withQ0 (by linarith)
          (by linarith) (hq G).2) hCA hCT hd2 hD hB
        (hq G).1 (hdim G) (le_trans (by gcongr; exact_mod_cast (hq G).2) (hBσ G)) _ hNd
        hal hh hgood hdist R₀ hblk (fun c _ => halive G _) t.1 t.2
      exact ⟨R, fun _ => hR, fun h' => absurd hh h'⟩
    · exact ⟨ModeSystem.PaperRepClass.trivial (Ms G) (S.withQ0 (q G)) hA (S.sideParams δs) 10 h,
        fun h' => absurd h' hh, fun _ => rfl⟩
  choose R hR hR0 using hRex
  refine ⟨R, fun h hh t G => hR h t G hh, ?_⟩
  -- the instances
  have hX : ∀ h t G, (R h t G).Inst (fp.useInst (grp G) S.K (R h t G).Nd) := by
    intro h t G p hp
    obtain ⟨hpc, hu, hIJ, hb1, hb2⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_product.mp hpc).2, hIJ, hb1, hb2⟩
  have hXr : ∀ h t G, ∀ p ∈ fp.useInst (grp G) S.K (R h t G).Nd,
      p.2.1 ∈ Bs ∧ p.2.2.1 ∈ fp.retainedV (grp G) p.2.1 S.K := by
    intro h t G p hp
    have hpN := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    by_cases hh : h ≤ S.Jstar
    · rw [hR h t G hh] at hpN
      obtain ⟨bJ, hbJ, x, -, he⟩ := ((Ms G).mem_paperSuccNodes (S.withQ0 (q G)) hA).mp
          (Finset.mem_filter.mp hpN).1
      rw [he]
      exact (fp.mem_retainedPairs).mp hbJ
    · rw [hR0 h t G hh] at hpN
      exact absurd hpN (Finset.notMem_empty _)
  have hab : 6 * (4 * S.Dstar ^ 2 * CF) / S.Dstar ^ 59 ≤ S.Dstar⁻¹ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have e : S.Dstar⁻¹ ^ 2 * S.Dstar ^ 59 = S.Dstar ^ 2 * S.Dstar ^ 55 := by
      field_simp
    rw [e]
    have h2 : 0 ≤ S.Dstar ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hCFD h2
    linarith
  have hCH : (Finset.range (S.Jstar + 1) ×ˢ Ts ×ˢ Thr).Nonempty :=
    Finset.Nonempty.product ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (Finset.Nonempty.product hTs hThr0)
  exact fp.paper_first_top_count l s hT htag d mb hne hanc grp hgrp k hcol j hPH ls S hA
    (S.sideParams δs) Ms q hq L Bs c hcrep hcB hVE (Finset.range (S.Jstar + 1)) Ts Thr hThr hCH R
    (fun h t G => fp.useInst (grp G) S.K (R h t G).Nd) hX hXr hD hδ hΛ hQ0 Kf hbox hDg hKf hεw
    halive hpath hroot hτ hτ1 hHτ hNq hτN cc hcc hkq hDmq hDb hn hab hρ hρ1

end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.paper_tops_energy
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.paper_first_top_count
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.paper_first_top_count_main
