/-
Adapted from TrilinearHT/Auto/Sec13_4SideStatesFixedOffsets.lean,
Sec13_5RepresentativesComponentSizesFirstTops.lean and
Sec15_1ExactCommonHeightSelection.lean. Copyright (c) 2026 Joris Roos;
original authors: Claude. Apache-2.0.
V72 uses the actual manuscript goodness predicate in the local forms.
-/
import ReferenceV72PaperEventEnergy

namespace Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

noncomputable def paperCoreComps (b : ℤ) (J : ℤ × ℤ) : Finset (Finset Ms.Md) :=
  Ms.allComps S hA b J \ Ms.paperSideEvents S hA SP b J

theorem paperSideEvents_subset_allComps (b : ℤ) (J : ℤ × ℤ) :
    Ms.paperSideEvents S hA SP b J ⊆ Ms.allComps S hA b J := by
  intro E hE
  unfold paperSideEvents at hE
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

theorem paper_frozenEval_sub_side (b : ℤ) (J : ℤ × ℤ) (c : Ms.Md → ℂ) :
    Ms.frozenEval S b J c -
        ∑ E ∈ Ms.paperSideEvents S hA SP b J, ∑ m ∈ E, c m • Ms.cellMode J m =
      ∑ K ∈ Ms.paperCoreComps S hA SP b J, ∑ m ∈ K, c m • Ms.cellMode J m := by
  classical
  rw [Ms.frozenEval_eq_comps S hA b J c, paperCoreComps,
    ← Finset.sum_sdiff (Ms.paperSideEvents_subset_allComps S hA SP b J)]
  abel

noncomputable def paperBlockCore (b : ℤ) (cells : Finset (ℤ × ℤ)) (c : ℤ × ℤ → Ms.Md → ℂ) :
    ColumnL2 Ms.Md :=
  ∑ J ∈ cells, ∑ K ∈ Ms.paperCoreComps S hA SP b J, ∑ m ∈ K, c J m • Ms.cellMode J m

/-- Blueprint lines 2124-2133 (`Z̃ = A + V`): a column function supported on the disjoint retained
pre-cells of a block, which restricts on each of them to the frozen evaluation of its
coefficients, is the sum of the full core subtotal and the side subtotal of the block. Every
mode alive at the decision cell lies in exactly one minimal CURRENT component, which is either a
core component or a side event. -/
theorem paper_eq_blockCore_add_blockSide {b : ℤ} {cells : Finset (ℤ × ℤ)}
    (hdis : Set.PairwiseDisjoint (cells : Set (ℤ × ℤ)) fun J => dyadicGridCell Gd J.1 J.2)
    (c : ℤ × ℤ → Ms.Md → ℂ) (X : ColumnL2 Ms.Md)
    (hsupp : columnL2Restriction (⋃ J ∈ cells, dyadicGridCell Gd J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable Gd J.1 J.2) X = X)
    (hrep : ∀ J ∈ cells, columnL2Restriction (dyadicGridCell Gd J.1 J.2)
      (dyadicGridCell_measurable Gd J.1 J.2) X = Ms.frozenEval S b J (c J)) :
    X = Ms.paperBlockCore S hA SP b cells c + Ms.paperBlockSide S hA SP b cells c := by
  rw [← hsupp, columnL2Restriction_biUnion cells (fun J => dyadicGridCell Gd J.1 J.2)
    (fun J => dyadicGridCell_measurable Gd J.1 J.2) hdis, FunLike.coe_sum, Finset.sum_apply]
  unfold paperBlockCore paperBlockSide
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [hrep J hJ, ← Ms.paper_frozenEval_sub_side S hA SP b J (c J)]
  abel

def paperCompGood (b : ℤ) (J : ℤ × ℤ) (h : ℕ) (K : Finset Ms.Md) : Prop :=
  ∃ x : Ms.alive (ancAt Gd J (b - 4 * S.K)),
    K = ((Ms.blockComps S hA b J).E 0 x).map ⟨Subtype.val, Subtype.val_injective⟩ ∧
      (Ms.blockComps S hA b J).PaperGood SP.Δ (Ms.goodP S SP b) h x

open Classical in
theorem paperCompGood_iff {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    {x : Ms.alive (ancAt Gd J (b - 4 * S.K))}
    (hK : K = ((Ms.blockComps S hA b J).E 0 x).map ⟨Subtype.val, Subtype.val_injective⟩) (h : ℕ) :
    Ms.paperCompGood S hA SP b J h K ↔ (Ms.blockComps S hA b J).PaperGood SP.Δ (Ms.goodP S SP b) h x := by
  constructor
  · rintro ⟨x', hK', hg⟩
    have hE : (Ms.blockComps S hA b J).E 0 x = (Ms.blockComps S hA b J).E 0 x' := by
      rw [hK] at hK'
      exact Finset.map_injective _ hK'
    have hx : x ∈ (Ms.blockComps S hA b J).E 0 x' := by
      rw [← hE]; exact (Ms.blockComps S hA b J).E_self 0 x
    exact ((Ms.blockComps S hA b J).paper_good_minimal_pre SP.Δ (Ms.goodP S SP b) hx h).mp hg
  · intro hg
    exact ⟨x, hK, hg⟩

open Classical in
theorem paperCoreComps_rep {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    (hK : K ∈ Ms.paperCoreComps S hA SP b J) :
    ∃ x : Ms.alive (ancAt Gd J (b - 4 * S.K)),
      K = ((Ms.blockComps S hA b J).E 0 x).map ⟨Subtype.val, Subtype.val_injective⟩ ∧
      (Ms.blockComps S hA b J).PaperCore SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs x := by
  obtain ⟨hall, hside⟩ := Finset.mem_sdiff.mp hK
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hall
  refine ⟨x, rfl, ?_⟩
  by_contra hc
  exact hside (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩)

open Classical in
theorem paperCoreComp_bad_card {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    (hK : K ∈ Ms.paperCoreComps S hA SP b J) (hJ : 2 ≤ SP.Jst) (hδ : 0 < SP.δs)
    (hδ16 : SP.δs ≤ 1 / 16) :
    (((ModeComponents.upperHeights SP.Jst SP.δs).filter fun h =>
      ¬ Ms.paperCompGood S hA SP b J h K).card : ℝ) ≤
      2 * SP.δs * (ModeComponents.upperHeights SP.Jst SP.δs).card := by
  obtain ⟨x, hKx, hcore⟩ := Ms.paperCoreComps_rep S hA SP hK
  refine le_trans ?_ ((Ms.blockComps S hA b J).paper_core_bad_proportion SP.Δ (Ms.goodP S SP b) hJ hδ
    hδ16 hcore)
  have hsub : (ModeComponents.upperHeights SP.Jst SP.δs).filter
      (fun h => ¬ Ms.paperCompGood S hA SP b J h K) ⊆
      (Ms.blockComps S hA b J).paperBadHeights SP.Δ (Ms.goodP S SP b) SP.Jst x ∩
        ModeComponents.upperHeights SP.Jst SP.δs := by
    intro h hh
    obtain ⟨hup, hng⟩ := Finset.mem_filter.mp hh
    refine Finset.mem_inter.mpr ⟨?_, hup⟩
    unfold ModeComponents.paperBadHeights
    refine Finset.mem_filter.mpr ⟨?_, fun hg => hng ((Ms.paperCompGood_iff S hA SP hKx h).mpr hg)⟩
    exact (Finset.mem_filter.mp hup).1
  exact_mod_cast Finset.card_le_card hsub

/-- Reclassification preserves the full block subtotal. This also identifies
 the correction that must be moved from the old core to the new side. -/
theorem paper_block_balance (b : ℤ) (cells : Finset (ℤ × ℤ))
    (c : ℤ × ℤ → Ms.Md → ℂ) :
    Ms.blockCore S hA SP b cells c + Ms.blockSide S hA SP b cells c =
      Ms.paperBlockCore S hA SP b cells c + Ms.paperBlockSide S hA SP b cells c := by
  unfold blockCore blockSide paperBlockCore paperBlockSide
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Ms.frozenEval_sub_side S hA SP b J (c J),
    ← Ms.paper_frozenEval_sub_side S hA SP b J (c J)]
  abel

end ModeSystem

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)

open Classical in
noncomputable def paperCoreAt (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  if D.u = some l then 0 else
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
      (fp.physMain (D.Ms l G).Md ((D.Ms l G).paperBlockCore D.S D.hA D.SP (A.blkStart D.S.K I.1)
        (fp.retainedV G (A.blkStart D.S.K I.1) D.S.K) (D.c l G (A.blkStart D.S.K I.1))))

/-- Move the difference between the old and exact core to the side term.
The old side is projected to its physical coordinate. The
identity below preserves the physical output even if classifications differ. -/
noncomputable def paperSideAt (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  fp.physMain (bf.Lab ⊕ Fin fp.Mc) (D.toLeaf.sv l G I) +
    D.coreAt l G I - D.paperCoreAt l G I

/-- For a nonbasic slot the reclassified side is exactly the old coarse
 variation plus the paper-side block subtotal, on the actual cell. -/
open Classical in
theorem paperSideAt_basic (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ)
    (hl : D.u ≠ some l) :
    D.paperSideAt l G I =
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.basicOut l (D.cat l) (D.mbs l) G
          (D.Lf.role l) (D.Lf.layers l) I.1) -
         fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.frozenZ l (D.cat l) (D.mbs l) G
          (D.Lf.role l) (D.Lf.layers l) (A.blkStart D.S.K I.1 - 4 * D.S.K)) +
         fp.physMain (D.Ms l G).Md ((D.Ms l G).paperBlockSide D.S D.hA D.SP
          (A.blkStart D.S.K I.1) (fp.retainedV G (A.blkStart D.S.K I.1) D.S.K)
          (D.c l G (A.blkStart D.S.K I.1)))) := by
  have hsv := D.toLeaf_sv_basic hl G I
  have hgs : D.gs' l G I.1 = fp.sideState (D.Ms l G) l (D.cat l) (D.mbs l) G
      (D.Lf.role l) (D.Lf.layers l) D.S D.hA D.SP (D.c l G (A.blkStart D.S.K I.1))
      (A.blkStart D.S.K I.1) I.1 := rfl
  have hss : fp.physMain (bf.Lab ⊕ Fin fp.Mc) (D.gs' l G I.1) = D.gs' l G I.1 := by
    rw [hgs]
    unfold sideState
    rw [map_add, map_sub, fp.physMain_physMain, fp.physMain_physMain, fp.physMain_physMain]
  let b := A.blkStart D.S.K I.1
  let cells := fp.retainedV G b D.S.K
  let c := D.c l G b
  have hb := (D.Ms l G).paper_block_balance D.S D.hA D.SP b cells c
  have hb' := congrArg (fun x => columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2) (fp.physMain (D.Ms l G).Md x)) hb
  simp only [map_add] at hb'
  unfold paperSideAt
  rw [hsv, physEmbed_restrict, hss, hgs]
  simp only [coreAt, paperCoreAt, hl, ↓reduceIte]
  unfold sideState
  simp only [map_add, map_sub]
  dsimp [b, cells, c] at hb'
  have hmove :
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (D.Ms l G).Md ((D.Ms l G).blockSide D.S D.hA D.SP b cells c)) +
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (D.Ms l G).Md ((D.Ms l G).blockCore D.S D.hA D.SP b cells c)) -
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (D.Ms l G).Md ((D.Ms l G).paperBlockCore D.S D.hA D.SP b cells c)) =
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (D.Ms l G).Md ((D.Ms l G).paperBlockSide D.S D.hA D.SP b cells c)) := by
    rw [add_comm, hb']
    abel
  dsimp [b, cells, c] at hmove
  rw [← hmove]
  abel

open Classical in
theorem paper_phys_out_eq (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (l : Fin 4) (G : bf.Grp)
    (hrep : D.u ≠ some l → D.RepAt L l G I) :
    fp.physMain (bf.Lab ⊕ Fin fp.Mc) (D.toLeaf.out l G I) =
      D.paperCoreAt l G I + D.paperSideAt l G I + D.errAt L l G I := by
  rw [D.phys_out_eq L hI l G hrep]
  unfold paperSideAt
  abel

open Classical in
theorem paper_form_expand (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp)
    (hrep : ∀ l, D.u ≠ some l → D.RepAt L l G I) :
    fp.Λc I (fun l => D.toLeaf.out l G I) = ∑ σ : Fin 4 → Fin 3,
      fp.Λc I (patternPiece (fun l => D.paperCoreAt l G I) (fun l => D.paperSideAt l G I)
        (fun l => D.errAt L l G I) σ) := by
  rw [fp.Λc_phys]
  simp_rw [D.paper_phys_out_eq L hI _ G (hrep _)]
  exact form_pattern_expand _ _ _ _

open Classical in
noncomputable def paperCompsAt (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) : Finset (Finset (D.Ms l G).Md) :=
  if D.u ≠ some l ∧ D.preAt I ∈ fp.retainedV G (A.blkStart D.S.K I.1) D.S.K then
    (D.Ms l G).paperCoreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) else ∅

open Classical in
theorem paperCoreAt_eq_comps (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) :
    D.paperCoreAt l G I = ∑ K ∈ D.paperCompsAt l G I, D.compSub l G I K := by
  have hIJ := D.subset_preAt I
  unfold paperCoreAt paperCompsAt
  set b := A.blkStart D.S.K I.1 with hb
  set Jp := D.preAt I with hJp
  -- the retained pre-cells other than `Jp` contribute nothing on `I`
  have hoff : ∀ J ∈ fp.retainedV G b D.S.K, J ≠ Jp →
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.physMain (D.Ms l G).Md (∑ K ∈ (D.Ms l G).paperCoreComps D.S D.hA D.SP b J,
          ∑ m ∈ K, D.c l G b J m • (D.Ms l G).cellMode J m)) = 0 := by
    intro J hJ hne
    have hJ1 := ((fp.mem_retainedV).mp hJ).2.1
    have hJp1 : Jp.1 = b - 2 * D.S.K := rfl
    have hdisJ : Disjoint (dyadicGridCell A.G J.1 J.2) (dyadicGridCell A.G Jp.1 Jp.2) := by
      have h2 : J.2 ≠ Jp.2 := fun h => hne (Prod.ext (by rw [hJ1, hJp1]) h)
      rw [hJ1, hJp1] at *
      exact dyadicGridCell_pairwiseDisjoint A.G _ h2
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, map_smul, restrict_physEmbed_eq_zero _ (hdisJ.mono_right hIJ) _
      ((D.Ms l G).cellMode_vanish J m), smul_zero]
  by_cases hl : D.u = some l
  · simp [hl]
  by_cases hJ : Jp ∈ fp.retainedV G b D.S.K
  · simp only [hl, hJ, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    unfold ModeSystem.paperBlockCore
    rw [map_sum, map_sum, Finset.sum_eq_single_of_mem Jp hJ hoff, map_sum, map_sum]
    rfl
  · simp only [hl, hJ, ne_eq, not_false_eq_true, and_false, ↓reduceIte, Finset.sum_empty]
    unfold ModeSystem.paperBlockCore
    rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun J hJ' => hoff J hJ' fun h => hJ (h ▸ hJ')

open Classical in
def paperSlotGood (G : bf.Grp) (I : ℤ × ℤ) (l : Fin 4) (h : ℕ)
    (o : Option (Finset (D.Ms l G).Md)) : Prop :=
  match o with
  | some K => (D.Ms l G).paperCompGood D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h K
  | none => True

open Classical in
/-- Blueprint lines 2464-2466 ("each core mode has bad proportion at most `2δ_*`, so success
probability is at least `1 - 2 m₀ δ_*`"): every tuple of core components of a pattern on a cell
has an upper height at which all its slots are good. -/
theorem paper_tuple_success (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) (hJ : 2 ≤ D.SP.Jst)
    (hδ : 0 < D.SP.δs) (hδ16 : D.SP.δs ≤ 1 / 16) :
    ∀ r ∈ Fintype.piFinset (compIdx σ (fun l => D.paperCompsAt l G I)),
      ((ModeComponents.upperHeights D.SP.Jst D.SP.δs).filter
        fun h => ∀ l, D.paperSlotGood G I l h (r l)).Nonempty := by
  intro r hr
  set H := ModeComponents.upperHeights D.SP.Jst D.SP.δs
  have hHn := ActiveSetup.AttemptParams.LeafSplit.upperHeights_nonempty (J := D.SP.Jst) hδ16
  set bad : Fin 4 → Finset ℕ := fun l => H.filter fun h => ¬ D.paperSlotGood G I l h (r l)
  have hbad : ∀ l, ((bad l ∩ H).card : ℝ) ≤ 2 * D.SP.δs * H.card := by
    intro l
    have hsub : bad l ∩ H ⊆ bad l := Finset.inter_subset_left
    refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
    have hrl := (Fintype.mem_piFinset.mp hr) l
    unfold compIdx at hrl
    split_ifs at hrl with hl
    · obtain ⟨K, hK, hrK⟩ := Finset.mem_map.mp hrl
      have hK' : K ∈ (D.Ms l G).paperCoreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) := by
        unfold paperCompsAt at hK
        beta_reduce at hK
        split_ifs at hK
        · exact hK
        · exact absurd hK (Finset.notMem_empty _)
      have e : bad l = H.filter fun h => ¬ (D.Ms l G).paperCompGood D.S D.hA D.SP
          (A.blkStart D.S.K I.1) (D.preAt I) h K := by
        simp only [bad, ← hrK, paperSlotGood, Function.Embedding.some_apply]
      rw [e]
      exact (D.Ms l G).paperCoreComp_bad_card D.S D.hA D.SP hK' hJ hδ hδ16
    · have hrn : r l = none := Finset.mem_singleton.mp hrl
      have e : bad l = ∅ := by
        simp only [bad, hrn, paperSlotGood, not_true_eq_false]
        exact Finset.filter_false_of_mem fun _ _ => id
      rw [e, Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
      positivity
  have hpos := success_proportion_pos H hHn bad hbad (by norm_num; linarith)
  have hne : (H.filter fun h => ∀ l, h ∉ bad l).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.card_empty, Nat.cast_zero, zero_div] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h, hh⟩ := hne
  obtain ⟨hH, hall⟩ := Finset.mem_filter.mp hh
  refine ⟨h, Finset.mem_filter.mpr ⟨hH, fun l => ?_⟩⟩
  by_contra hng
  exact hall l (Finset.mem_filter.mpr ⟨hH, hng⟩)

open Classical in
/-- Blueprint lines 2463-2466, the exact common-height selection on one actual cell and group of
the side states: the form of a core/side/error pattern is the sum over the tuples of core
components of the forms of their subtotals (the finite multilinear expansion), and it is the
convergent sum over the trial counts `n`, the assignments `a` of the failed trials to their first
failing roles, the words `w` of failed upper heights and the final heights `h`, with the weights
`|H|^{-(n+1)}` of the uniformly sampled heights, of the sums over the tuples in the product
masks; the first-success rule has total weight one for every tuple. -/
theorem paper_pattern_first_success (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md)
    (I : ℤ × ℤ) (G : bf.Grp) (σ : Fin 4 → Fin 3) (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) :
    fp.Λc I (patternPiece (fun l => D.paperCoreAt l G I) (fun l => D.paperSideAt l G I)
        (fun l => D.errAt L l G I) σ) =
      ∑ r ∈ Fintype.piFinset (compIdx σ (fun l => D.paperCompsAt l G I)),
        fp.Λc I (compSlot σ (fun l K => D.compSub l G I K) (fun l => D.paperSideAt l G I)
          (fun l => D.errAt L l G I) r) ∧
    HasSum (fun n : ℕ => ∑ a : Fin n → Fin 4,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      ∑ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
        (((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ) ^ (n + 1))⁻¹ •
        ∑ r ∈ (Fintype.piFinset (compIdx σ (fun l => D.paperCompsAt l G I))).filter
          (fun r => ∀ l, roleMask (D.paperSlotGood G I l) l a w h (r l)),
          fp.Λc I (compSlot σ (fun l K => D.compSub l G I K) (fun l => D.paperSideAt l G I)
            (fun l => D.errAt L l G I) r))
      (fp.Λc I (patternPiece (fun l => D.paperCoreAt l G I) (fun l => D.paperSideAt l G I)
        (fun l => D.errAt L l G I) σ)) := by
  have hexp : fp.Λc I (patternPiece (fun l => D.paperCoreAt l G I) (fun l => D.paperSideAt l G I)
      (fun l => D.errAt L l G I) σ) =
      ∑ r ∈ Fintype.piFinset (compIdx σ (fun l => D.paperCompsAt l G I)),
        fp.Λc I (compSlot σ (fun l K => D.compSub l G I K) (fun l => D.paperSideAt l G I)
          (fun l => D.errAt L l G I) r) :=
    pattern_comp_expand (fp.Λc I) σ (fun l => D.paperCompsAt l G I) (fun l K => D.compSub l G I K)
      _ _ _ fun l _ => D.paperCoreAt_eq_comps l G I
  refine ⟨hexp, ?_⟩
  rw [hexp]
  exact first_success_masked _ _ (fun l h o => D.paperSlotGood G I l h o) _
    (D.paper_tuple_success G I σ hJ hδ hδ16)

end SideInput
end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ModeSystem.paperSideEvents_subset_allComps
#print axioms Auto.ModeSystem.paper_frozenEval_sub_side
#print axioms Auto.ModeSystem.paper_eq_blockCore_add_blockSide
#print axioms Auto.ModeSystem.paperCompGood_iff
#print axioms Auto.ModeSystem.paperCoreComps_rep
#print axioms Auto.ModeSystem.paperCoreComp_bad_card
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_phys_out_eq
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_form_expand
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperCoreAt_eq_comps
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_tuple_success
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_pattern_first_success
#print axioms Auto.ModeSystem.paper_block_balance
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperSideAt_basic
