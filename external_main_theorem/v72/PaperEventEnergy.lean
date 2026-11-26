/-
Adapted from TrilinearHT/Auto/Sec13_3BesselRowsLinearSideEnergy.lean.
Copyright (c) 2026 Joris Roos; original authors: Claude. Apache-2.0.
V72 applies the original geometric row arguments to the stronger PaperCore
classification. The exact floor-log chain theorem from V71 supplies the
longest-chain bound; no subset assumption relating the two side families.
-/
import ReferenceV71PaperDensity

namespace Auto
open MeasureTheory Metric OpenAI086.AdaptedV56
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

theorem paperSideEvents_pair {b : ℤ} {J : ℤ × ℤ} (hJ : J.1 ≤ b + S.K) {E E' : Finset Ms.Md}
    (hE : E ∈ Ms.paperSideEvents S hA SP b J) (hE' : E' ∈ Ms.paperSideEvents S hA SP b J)
    (hne : E ≠ E') :
    Disjoint E E' ∧ ∀ m ∈ E, ∀ m' ∈ E', ¬ Ms.pre0Edge S J m m' := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨x', -, rfl⟩ := Finset.mem_image.mp hE'
  rw [Ms.blockComps_eq S hA hJ] at hne ⊢
  set C := Ms.preComps S hA (b - 4 * S.K) (b + S.K) J hJ
  have key : ∀ y y', y ∈ C.E 0 x → y' ∈ C.E 0 x' → (y = y' ∨ Ms.pre0Edge S J y.1 y'.1) →
      C.E 0 x = C.E 0 x' := by
    intro y y' hy hy' hyy
    have hy'y : y' ∈ C.E 0 y := by
      rcases hyy with heq | hedge
      · rw [heq]; exact C.E_self 0 y'
      · simp only [C, preComps, ModeSchedule.preCurrent, ModeComponents.ofEdges,
          Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hne' : y = y'
        · rw [hne']
        · exact SimpleGraph.Adj.reachable (by
            simp only [SimpleGraph.fromRel_adj]
            exact ⟨hne', Or.inl hedge⟩)
    rw [C.E_eq_of_mem hy, C.E_eq_of_mem hy', C.E_eq_of_mem hy'y]
  constructor
  · rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hm
    obtain ⟨y', hy', hyy⟩ := Finset.mem_map.mp hm'
    exact hne (by rw [key y y' hy hy' (Or.inl (Subtype.ext hyy.symm))])
  · intro m hm m' hm' hedge
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hm
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hm'
    exact hne (by rw [key y y' hy hy' (Or.inr hedge)])

theorem paperSideEvents_nonempty {b : ℤ} {J : ℤ × ℤ} {E : Finset Ms.Md}
    (hE : E ∈ Ms.paperSideEvents S hA SP b J) : E.Nonempty := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  exact ⟨x.1, Finset.mem_map.mpr ⟨x, ModeComponents.E_self _ 0 x, rfl⟩⟩

theorem paperSideEvents_alive {b : ℤ} {J : ℤ × ℤ} (hJ : b - 4 * S.K ≤ J.1) {E : Finset Ms.Md}
    (hE : E ∈ Ms.paperSideEvents S hA SP b J) {m : Ms.Md} (hm : m ∈ E) :
    dyadicGridCell Gd J.1 J.2 ⊆ dyadicGridCell Gd (Ms.cellOf m).1 (Ms.cellOf m).2 := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hm
  exact (subset_ancAt Gd J hJ).trans ((Ms.mem_alive).mp y.2)

open Classical in
theorem paper_class_rows (s : Finset Ms.Event)
    (hev : ∀ e ∈ s, e.2.2 ∈ Ms.paperSideEvents S hA SP e.1 e.2.1)
    (hdepth : ∀ e ∈ s, e.2.1.1 = e.1 - 2 * S.K) {L : ℕ}
    (hL : ∀ k e, LinkedChain (s : Set Ms.Event) (Ms.Linked S) k e → k ≤ L)
    (hδ : 0 < Ms.δc) (hΛ : 8 * Ms.Λ ≤ S.Ξ) (hΞ : 0 < S.Ξ) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0) {ε D : ℝ} (hε : 0 < ε)
    (hεw : ∀ m, ε ≤ Ms.L.εM m) (hD0 : 0 ≤ D) (hD1 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ D)
    (hD2 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ ε * D ^ 2)
    [inst : ∀ e, (Submodule.span ℂ ((Ms.evMode e) '' (e.2.2 : Set Ms.Md))).HasOrthogonalProjection]
    (F : ColumnL2 Ms.Md) :
    ∑ e ∈ s, ‖(Submodule.span ℂ ((Ms.evMode e) '' (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 ≤
      (L + 1) * ((1 + pairConst Ms.zc.dim Ms.δc S.Ξ Kf * D ^ 3) * ‖F‖ ^ 2) := by
  set! lev : Ms.Event → ℕ := chainLevel (s : Set Ms.Event) (Ms.Linked S) L
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.range (L + 1)) (g := lev)
    (fun e _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (chainLevel_le _ _ L e)))]
  calc ∑ ℓ ∈ Finset.range (L + 1), ∑ e ∈ s.filter (fun e => lev e = ℓ),
        ‖(Submodule.span ℂ ((Ms.evMode e) '' (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 ≤
      ∑ _ℓ ∈ Finset.range (L + 1),
        (1 + pairConst Ms.zc.dim Ms.δc S.Ξ Kf * D ^ 3) * ‖F‖ ^ 2 := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        refine Ms.level_rows S hδ (fun e he => ?_) (fun e he m hm => ?_)
          (fun e he => hdepth e (Finset.mem_filter.mp he).1) (fun e he e' he' hne hb hJ => ?_)
          (fun e he e' he' hlink => ?_) hΛ hΞ hQ0 Kf hbox hε hεw hD0 hD1 hD2 F
        · exact Ms.paperSideEvents_nonempty S hA SP (hev e (Finset.mem_filter.mp he).1)
        · have he1 := (Finset.mem_filter.mp he).1
          exact Ms.paperSideEvents_alive S hA SP (by rw [hdepth e he1]; omega) (hev e he1) hm
        · have he1 := (Finset.mem_filter.mp he).1
          have he1' := (Finset.mem_filter.mp he').1
          have hEne : e.2.2 ≠ e'.2.2 := by
            intro h
            exact hne (Prod.ext hb (Prod.ext hJ h))
          have h1 := hev e he1
          have h2 := hev e' he1'
          rw [← hb, ← hJ] at h2
          exact Ms.paperSideEvents_pair S hA SP (by rw [hdepth e he1]; omega) h1 h2 hEne
        · have he1 := (Finset.mem_filter.mp he).1
          have he1' := (Finset.mem_filter.mp he').1
          have hlt := chainLevel_lt (s : Set Ms.Event) (Ms.Linked S) hL he1 he1' hlink
          have h1 := (Finset.mem_filter.mp he).2
          have h2 := (Finset.mem_filter.mp he').2
          simp only [lev] at h1 h2
          omega
    _ = (L + 1) * ((1 + pairConst Ms.zc.dim Ms.δc S.Ξ Kf * D ^ 3) * ‖F‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem paperSideEvents_subset_alive {b : ℤ} {J : ℤ × ℤ} {E : Finset Ms.Md}
    (hE : E ∈ Ms.paperSideEvents S hA SP b J) : E ⊆ Ms.alive (ancAt Gd J (b - 4 * S.K)) := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  intro m hm
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hm
  exact y.2

/-- Modes of a side event are not adjacent at height zero to the other alive modes of the
pre-cell. -/
theorem paperSideEvent_not_adj {b : ℤ} {J : ℤ × ℤ} (hJ : J.1 ≤ b + S.K) {E : Finset Ms.Md}
    (hE : E ∈ Ms.paperSideEvents S hA SP b J) {m m' : Ms.Md} (hm : m ∈ E)
    (hm' : m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ E) : ¬ Ms.pre0Edge S J m m' := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  rw [Ms.blockComps_eq S hA hJ] at hm hm'
  obtain ⟨hm'A, hm'E⟩ := Finset.mem_sdiff.mp hm'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hm
  intro hedge
  set C := Ms.preComps S hA (b - 4 * S.K) (b + S.K) J hJ
  set! z : Ms.alive (ancAt Gd J (b - 4 * S.K)) := ⟨m', hm'A⟩
  have hz : z ∈ C.E 0 y := by
    simp only [C, preComps, ModeSchedule.preCurrent, ModeComponents.ofEdges, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hne : y = z
    · rw [hne]
    · exact SimpleGraph.Adj.reachable (by
        simp only [SimpleGraph.fromRel_adj]
        exact ⟨hne, Or.inl hedge⟩)
  have : z ∈ C.E 0 x := by rw [C.E_eq_of_mem hy]; exact hz
  exact hm'E (Finset.mem_map.mpr ⟨z, this, rfl⟩)

/-- Blueprint lines 2112-2113 for a side event: the row projection of the frozen evaluation
`Σ_{m alive} c_m Ψ_m` on the event's modes differs from the exact side subtotal by at most the
complementary pairing bound. -/
theorem paper_event_subtotal_close {b : ℤ} {J : ℤ × ℤ} (hJ : J.1 ≤ b + S.K)
    (hJu : b - 4 * S.K ≤ J.1) {E : Finset Ms.Md} (hE : E ∈ Ms.paperSideEvents S hA SP b J)
    (c : Ms.Md → ℂ)
    [(Submodule.span ℂ ((Ms.cellMode J) '' (E : Set Ms.Md))).HasOrthogonalProjection]
    (hδ : 0 < Ms.δc) (hΛ : 8 * Ms.Λ ≤ S.Ξ) (hΞ : 0 < S.Ξ) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0) {ε : ℝ} (hε : 0 < ε)
    (hεw : ∀ m, ε ≤ Ms.L.εM m) :
    ‖(Submodule.span ℂ ((Ms.cellMode J) '' (E : Set Ms.Md))).starProjection
        (∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), c m • Ms.cellMode J m) -
        ∑ m ∈ E, c m • Ms.cellMode J m‖ ≤
      pairConst Ms.zc.dim Ms.δc S.Ξ Kf * dyadicGridLength Gd J.1 *
        (Real.sqrt E.card * (Real.sqrt (Ms.alive (ancAt Gd J (b - 4 * S.K)) \ E).card *
          Real.sqrt (∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ E, ‖c m'‖ ^ 2))) /
        Real.sqrt (ε * dyadicGridLength Gd J.1) := by
  have hr := dyadicGridLength_pos Gd J.1
  have hsub := Ms.paperSideEvents_subset_alive S hA SP hE
  have hJU := subset_ancAt Gd J hJu
  refine projection_subtotal_close E _ hsub (Ms.cellMode J) c
    (mul_nonneg (pairConst_nonneg _ hδ hΞ Kf) hr.le) (mul_pos hε hr) (fun m hm m' hm' => ?_)
    (fun c' => ?_)
  · have hmA := hsub hm
    have hm'A := (Finset.mem_sdiff.mp hm').1
    have hne : m ≠ m' := fun h => (Finset.mem_sdiff.mp hm').2 (h ▸ hm)
    exact Ms.cellMode_inner_le S hδ hΛ hΞ hQ0 Kf hbox (hJU.trans ((Ms.mem_alive).mp hmA))
      (hJU.trans ((Ms.mem_alive).mp hm'A)) hne (Ms.paperSideEvent_not_adj S hA SP hJ hE hm hm')
  · have h := augMode_toLp_sum_norm_sq_ge (dyadicGridCell_measurable Gd J.1 J.2)
      (dyadicGridCell_volume_ne_top Gd J) Ms.wave Ms.wave_measurable Ms.wave_norm_le Ms.L.εM E c'
      (fun m _ => hεw m) hε.le
    have hv : volume.real (dyadicGridCell Gd J.1 J.2) = dyadicGridLength Gd J.1 := by
      rw [measureReal_def, dyadicGridCell_volume, ENNReal.toReal_ofReal hr.le]
    rw [hv] at h
    exact h

noncomputable def paperBlockSide (b : ℤ) (cells : Finset (ℤ × ℤ)) (c : ℤ × ℤ → Ms.Md → ℂ) :
    ColumnL2 Ms.Md :=
  ∑ J ∈ cells, ∑ E ∈ Ms.paperSideEvents S hA SP b J, ∑ m ∈ E, c J m • Ms.cellMode J m

/-- Blueprint lines 2116-2118 for one block: the side subtotal over disjoint retained pre-cells is
almost orthogonal over its paperEvents. -/
theorem paperBlockSide_norm_sq_le {b : ℤ} {cells : Finset (ℤ × ℤ)}
    (hdepth : ∀ J ∈ cells, J.1 = b - 2 * S.K) (c : ℤ × ℤ → Ms.Md → ℂ)
    (hδ : 0 < Ms.δc) (hΛ : 8 * Ms.Λ ≤ S.Ξ) (hΞ : 0 < S.Ξ) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0) {ε D : ℝ} (hε : 0 < ε)
    (hεw : ∀ m, ε ≤ Ms.L.εM m) (hD0 : 0 ≤ D) (hD1 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ D)
    (hD2 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ ε * D ^ 2) :
    ‖Ms.paperBlockSide S hA SP b cells c‖ ^ 2 ≤
      (1 + pairConst Ms.zc.dim Ms.δc S.Ξ Kf * D ^ 3) *
        ∑ J ∈ cells, ∑ E ∈ Ms.paperSideEvents S hA SP b J, ‖∑ m ∈ E, c J m • Ms.cellMode J m‖ ^ 2 := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  refine block_subtotals_le cells (fun J => dyadicGridCell Gd J.1 J.2)
    (fun J => dyadicGridCell_measurable Gd J.1 J.2) (fun J => dyadicGridCell_volume_ne_top Gd J)
    ?_ (fun J => Ms.paperSideEvents S hA SP b J) Ms.wave Ms.wave_measurable Ms.wave_norm_le Ms.L.εM c
    (pairConst_nonneg _ hδ hΞ Kf) hε hD0 ?_ ?_ hεw ?_ ?_
  · -- distinct pre-cells of one depth are disjoint
    intro J hJ J' hJ' hne
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    by_contra hov
    exact hne (dyadicGridCell_eq_of_meet Gd ((hdepth J hJ).trans (hdepth J' hJ').symm)
      (Set.nonempty_iff_ne_empty.mpr hov))
  · intro J hJ E hE E' hE' hne
    exact (Ms.paperSideEvents_pair S hA SP (by rw [hdepth J hJ]; omega) hE hE' hne).1
  · intro J hJ E hE E' hE' hne m hm m' hm'
    have hpair := Ms.paperSideEvents_pair S hA SP (by rw [hdepth J hJ]; omega) hE hE' hne
    have hmm : m ≠ m' := fun h => Finset.disjoint_left.mp hpair.1 hm (h ▸ hm')
    have hJu : b - 4 * S.K ≤ J.1 := by rw [hdepth J hJ]; omega
    have h := Ms.cellMode_inner_le S hδ hΛ hΞ hQ0 Kf hbox
      (Ms.paperSideEvents_alive S hA SP hJu hE hm) (Ms.paperSideEvents_alive S hA SP hJu hE' hm') hmm
      (hpair.2 m hm m' hm')
    unfold cellMode at h
    rw [inner_augMode_toLp_ne (dyadicGridCell_measurable Gd J.1 J.2)
      (dyadicGridCell_volume_ne_top Gd J) (Ms.wave_measurable m) (Ms.wave_norm_le m)
      (Ms.wave_measurable m') (Ms.wave_norm_le m') _ _ hmm] at h
    have hv : volume.real (dyadicGridCell Gd J.1 J.2) = dyadicGridLength Gd J.1 := by
      rw [measureReal_def, dyadicGridCell_volume,
        ENNReal.toReal_ofReal (dyadicGridLength_pos Gd J.1).le]
    rw [hv]; exact h
  · -- the number of paperEvents on a pre-cell, counted along the path through its left endpoint
    intro J hJ
    have hJu : b - 4 * S.K ≤ J.1 := by rw [hdepth J hJ]; omega
    have hy : dyadicGridLeft Gd J.1 J.2 ∈ dyadicGridCell Gd J.1 J.2 :=
      Set.left_mem_Ico.mpr (by linarith [dyadicGridLength_pos Gd J.1])
    refine le_trans (Nat.cast_le.mpr ?_) (hD1 (dyadicGridLeft Gd J.1 J.2))
    refine card_le_of_pairwiseDisjoint_subset _ id _ (fun E hE => ?_) (fun E hE m hm => ?_)
      (fun E hE E' hE' hne => ?_)
    · exact Ms.paperSideEvents_nonempty S hA SP hE
    · exact (Ms.mem_ptSet).mpr (Ms.paperSideEvents_alive S hA SP hJu hE hm hy)
    · exact (Ms.paperSideEvents_pair S hA SP (by rw [hdepth J hJ]; omega) hE hE' hne).1
  · intro J hJ E hE
    have hJu : b - 4 * S.K ≤ J.1 := by rw [hdepth J hJ]; omega
    have hy : dyadicGridLeft Gd J.1 J.2 ∈ dyadicGridCell Gd J.1 J.2 :=
      Set.left_mem_Ico.mpr (by linarith [dyadicGridLength_pos Gd J.1])
    refine le_trans (Nat.cast_le.mpr ?_) (hD2 (dyadicGridLeft Gd J.1 J.2))
    exact Finset.card_le_card fun m hm =>
      (Ms.mem_ptSet).mpr (Ms.paperSideEvents_alive S hA SP hJu hE hm hy)

theorem paper_group_side_energy (Bs : Finset ℤ) (cells : ℤ → Finset (ℤ × ℤ))
    (hdepth : ∀ b ∈ Bs, ∀ J ∈ cells b, J.1 = b - 2 * S.K) (c : ℤ → ℤ × ℤ → Ms.Md → ℂ)
    [inst : ∀ (J : ℤ × ℤ) (E : Finset Ms.Md),
      (Submodule.span ℂ ((Ms.cellMode J) '' (E : Set Ms.Md))).HasOrthogonalProjection]
    (hδ : 0 < Ms.δc) (hΛ : 8 * Ms.Λ ≤ S.Ξ) (hΞ : 0 < S.Ξ) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0) {ε D : ℝ} (hε : 0 < ε)
    (hεw : ∀ m, ε ≤ Ms.L.εM m) (hD0 : 0 ≤ D) (hD1 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ D)
    (hD2 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ ε * D ^ 2) :
    ∑ b ∈ Bs, ‖Ms.paperBlockSide S hA SP b (cells b) (c b)‖ ^ 2 ≤
      2 * (1 + pairConst Ms.zc.dim Ms.δc S.Ξ Kf * D ^ 3) *
        ∑ b ∈ Bs, ∑ J ∈ cells b, ∑ E ∈ Ms.paperSideEvents S hA SP b J,
          (‖(Submodule.span ℂ ((Ms.cellMode J) '' (E : Set Ms.Md))).starProjection
              (Ms.frozenEval S b J (c b J))‖ ^ 2 +
            Ms.eventErr S Kf ε b J E (c b J) ^ 2) := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hc0 : 0 ≤ 1 + pairConst Ms.zc.dim Ms.δc S.Ξ Kf * D ^ 3 := by
    have := pairConst_nonneg Ms.zc.dim hδ hΞ Kf; positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  refine (Ms.paperBlockSide_norm_sq_le S hA SP (hdepth b hb) (c b) hδ hΛ hΞ hQ0 Kf hbox hε hεw hD0
    hD1 hD2).trans ?_
  rw [mul_assoc, ← mul_assoc 2, mul_comm 2, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun J hJ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun E hE => ?_
  have hd := hdepth b hb J hJ
  have h := Ms.paper_event_subtotal_close S hA SP (by rw [hd]; omega) (by rw [hd]; omega) hE (c b J)
    hδ hΛ hΞ hQ0 Kf hbox hε hεw
  set P := (Submodule.span ℂ ((Ms.cellMode J) '' (E : Set Ms.Md))).starProjection
    (Ms.frozenEval S b J (c b J))
  set T := ∑ m ∈ E, c b J m • Ms.cellMode J m
  set er := Ms.eventErr S Kf ε b J E (c b J)
  have h' : ‖P - T‖ ≤ er := h
  have hT : ‖T‖ ≤ ‖P‖ + er := by
    have := norm_sub_norm_le T P
    rw [norm_sub_rev] at this
    linarith
  have hT0 := norm_nonneg T
  have hP0 := norm_nonneg P
  have her : 0 ≤ er := (norm_nonneg _).trans h'
  nlinarith only [sq_nonneg (‖P‖ - er), hT, hT0]

noncomputable def paperEvents (Bs : Finset ℤ) (cells : ℤ → Finset (ℤ × ℤ)) : Finset Ms.Event := by
  classical exact Bs.biUnion fun b => (cells b).biUnion fun J =>
    (Ms.paperSideEvents S hA SP b J).image fun E => (b, J, E)

theorem paper_sum_events (Bs : Finset ℤ) (cells : ℤ → Finset (ℤ × ℤ)) (f : Ms.Event → ℝ) :
    ∑ e ∈ Ms.paperEvents S hA SP Bs cells, f e =
      ∑ b ∈ Bs, ∑ J ∈ cells b, ∑ E ∈ Ms.paperSideEvents S hA SP b J, f (b, J, E) := by
  classical
  unfold paperEvents
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.sum_image]
      intro E _ E' _ h
      exact (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2
    · intro J _ J' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro e he he'
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨E', -, h⟩ := Finset.mem_image.mp he'
      exact hne (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).1.symm
  · intro b _ b' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨J, -, hJ⟩ := Finset.mem_biUnion.mp he
    obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨J', -, hJ'⟩ := Finset.mem_biUnion.mp he'
    obtain ⟨E', -, h⟩ := Finset.mem_image.mp hJ'
    exact hne (Prod.ext_iff.mp h).1.symm

theorem paper_mem_events {Bs : Finset ℤ} {cells : ℤ → Finset (ℤ × ℤ)} {e : Ms.Event}
    (he : e ∈ Ms.paperEvents S hA SP Bs cells) :
    e.1 ∈ Bs ∧ e.2.1 ∈ cells e.1 ∧ e.2.2 ∈ Ms.paperSideEvents S hA SP e.1 e.2.1 := by
  classical
  unfold paperEvents at he
  obtain ⟨b, hb, hJ⟩ := Finset.mem_biUnion.mp he
  obtain ⟨J, hJc, hE⟩ := Finset.mem_biUnion.mp hJ
  obtain ⟨E, hEs, rfl⟩ := Finset.mem_image.mp hE
  exact ⟨hb, hJc, hEs⟩

end ModeSystem

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc)

open Classical in
theorem paper_group_event_rows_schedule (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCj : 340 ≤ Cj) (hCA : 1 ≤ CA) (hδs : 0 < δs)
    (hδ1 : δs ≤ 1) (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (hQ : 1 ≤ S.Q0)
    (hDm : 2 ≤ S.Dm) (hW : 8 * ((S.dmax : ℝ) + 1) ^ 3 * Real.log (2 * S.H) / Real.log 2 ≤ W)
    (hdim : ∀ p, Ms.dvOf p + Ms.zc.dim ≤ S.dmax) {M : ℕ} (hM1 : 1 ≤ M)
    (hMD : (M : ℝ) ≤ 2 * S.Dm) (hM : ∀ U : ℤ × ℤ, ((Ms.alive U).image Ms.keyOf).card ≤ M)
    (R₀ : ℤ) (Bs : Finset ℤ) (cells : ℤ → Finset (ℤ × ℤ))
    (hdepth : ∀ b ∈ Bs, ∀ J ∈ cells b, J.1 = b - 2 * S.K)
    (hgrid : ∀ b ∈ Bs, (S.K : ℤ) ∣ b - R₀) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (Kf : ℕ)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hBox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Bstar) (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (hpt : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ S.Dstar)
    [inst : ∀ (J : ℤ × ℤ) (E : Finset Ms.Md),
      (Submodule.span ℂ ((Ms.cellMode J) '' (E : Set Ms.Md))).HasOrthogonalProjection]
    (F : ColumnL2 Ms.Md) :
    ∑ e ∈ Ms.paperEvents S (hV.six_le_A0 hCA hd2 hD hB) (S.sideParams δs) Bs cells,
        ‖(Submodule.span ℂ ((Ms.cellMode e.2.1) '' (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 ≤
      6 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1) * ‖F‖ ^ 2 := by
  have hA := hV.six_le_A0 hCA hd2 hD hB
  set SP := S.sideParams δs
  set ev := Ms.paperEvents S hA SP Bs cells
  set L := ⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊
  have hD1 : (1 : ℝ) ≤ S.Dstar := by linarith
  have hDp : 0 < S.Dstar := by linarith
  -- the block length is positive
  obtain ⟨κ, hκ⟩ := hV.K_dyadic
  have hK1 : 1 ≤ S.K := by rw [hκ]; exact Nat.one_le_two_pow
  -- the numerical side conditions of lem:mode-rows
  have hΞ : 0 < S.Ξ := pow_pos hDp 1000
  have hΛ8 : 8 * Ms.Λ ≤ S.Ξ := by
    have h1 : 8 * S.Dstar ≤ S.Dstar ^ 1000 := by
      have h4 : S.Dstar ^ 4 ≤ S.Dstar ^ 1000 := pow_le_pow_right₀ hD1 (by norm_num)
      have h16 : (16 : ℝ) ≤ S.Dstar ^ 4 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hD 4)
      have h3 : 8 * S.Dstar ≤ S.Dstar ^ 4 := by
        have : S.Dstar ^ 4 = S.Dstar * S.Dstar ^ 3 := by ring
        have h8 : (8 : ℝ) ≤ S.Dstar ^ 3 :=
          le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hD 3)
        nlinarith only [hD, h8]
      linarith
    have : 8 * Ms.Λ ≤ 8 * S.Dstar := by linarith
    exact this.trans h1
  have hQ0 : 0 < S.Q0 := by omega
  have hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0 := by
    have hBA : S.Bstar ≤ S.A0 := by
      have hb := hV.base_le_A0 hCA hd2 hD hB
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
  have hε : 0 < S.Dstar⁻¹ := inv_pos.mpr hDp
  have hpt2 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ S.Dstar⁻¹ * S.Dstar ^ 2 := fun y => by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hDp.ne', one_mul]; exact hpt y
  have hη : pairConst Ms.zc.dim Ms.δc S.Ξ Kf * S.Dstar ^ 3 ≤ 1 := by
    have h := S.pairConst_mul_le hD hDg hKf
    have h0 := pairConst_nonneg Ms.zc.dim hδ hΞ Kf
    have h3 : S.Dstar ^ 3 ≤ S.Dstar ^ 200 := pow_le_pow_right₀ hD1 (by norm_num)
    exact (mul_le_mul_of_nonneg_left h3 h0).trans h
  -- each class of blocks
  have hclass : ∀ i : Fin 3, ∑ e ∈ ev.filter (fun e => blockClass R₀ S.K e.1 = i),
      ‖(Submodule.span ℂ ((Ms.cellMode e.2.1) '' (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 ≤
        (L + 1) * (2 * ‖F‖ ^ 2) := by
    intro i
    set s := ev.filter (fun e => blockClass R₀ S.K e.1 = i)
    have hmem : ∀ e ∈ s, e.1 ∈ Bs ∧ e.2.1 ∈ cells e.1 ∧
        e.2.2 ∈ Ms.paperSideEvents S hA SP e.1 e.2.1 ∧ blockClass R₀ S.K e.1 = i := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      exact ⟨(Ms.paper_mem_events S hA SP he1).1, (Ms.paper_mem_events S hA SP he1).2.1,
        (Ms.paper_mem_events S hA SP he1).2.2, he2⟩
    have hrows := Ms.paper_class_rows S hA SP s (fun e he => (hmem e he).2.2.1)
      (fun e he => hdepth e.1 (hmem e he).1 e.2.1 (hmem e he).2.1) (L := L) ?_ hδ hΛ8 hΞ hQ0 Kf
      hbox hε hεw (by linarith) (fun y => hpt y) hpt2 (inst := fun e => inst e.2.1 e.2.2) F
    · refine hrows.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hF := sq_nonneg ‖F‖
      nlinarith only [hη]
    -- the chain length of the class (`eq:bad-density`)
    intro k e hc
    have hb := Ms.paper_chain_length_valid S hV hCA hCj hδs hδ1 hd2 hD hB hQ hDm hW hdim hM1 hMD
      hM R₀ s (fun e he => (hmem e he).2.2.1)
      (fun e he => hdepth e.1 (hmem e he).1 e.2.1 (hmem e he).2.1)
      (fun e he => hgrid e.1 (hmem e he).1)
      (fun e he e' he' hlt => blockClass_sep hK1 (hgrid e.1 (hmem e he).1)
        (hgrid e'.1 (hmem e' he').1) (((hmem e he).2.2.2).trans ((hmem e' he').2.2.2).symm)
        hlt) hc
    have hk : (k : ℝ) ≤ (2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs) := by
      push_cast at hb; linarith
    exact Nat.le_floor hk
  have hsplit : ∑ e ∈ ev, ‖(Submodule.span ℂ ((Ms.cellMode e.2.1) ''
      (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 =
      ∑ i : Fin 3, ∑ e ∈ ev.filter (fun e => blockClass R₀ S.K e.1 = i), ‖(Submodule.span ℂ
        ((Ms.cellMode e.2.1) '' (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 :=
    (Finset.sum_fiberwise ev (fun e => blockClass R₀ S.K e.1) _).symm
  rw [hsplit]
  refine (Finset.sum_le_sum fun i _ => hclass i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end ModeSystem
end Auto

#print axioms Auto.ModeSystem.paperSideEvents_pair
#print axioms Auto.ModeSystem.paperSideEvents_nonempty
#print axioms Auto.ModeSystem.paperSideEvents_alive
#print axioms Auto.ModeSystem.paper_class_rows
#print axioms Auto.ModeSystem.paperSideEvents_subset_alive
#print axioms Auto.ModeSystem.paperSideEvent_not_adj
#print axioms Auto.ModeSystem.paper_event_subtotal_close
#print axioms Auto.ModeSystem.paperBlockSide_norm_sq_le
#print axioms Auto.ModeSystem.paper_group_side_energy
#print axioms Auto.ModeSystem.paper_sum_events
#print axioms Auto.ModeSystem.paper_mem_events
#print axioms Auto.ModeSystem.paper_group_event_rows_schedule
