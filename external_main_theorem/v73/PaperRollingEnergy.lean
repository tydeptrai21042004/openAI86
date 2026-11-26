/-
Adapted from TrilinearHT/Auto/Sec13_4SideStatesFixedOffsets.lean.
Copyright (c) 2026 Joris Roos; original authors: Claude. Apache-2.0.
V73 uses the new paper-specific block subtotal, not the old ratio-based one.
Both rolling budgets are unchanged since they do not depend on core classification.
Uncompiled proof candidates.
-/
import ReferenceV73PaperGlobalEnergy
import ReferenceV72PaperLocalForms

namespace Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
noncomputable def paperSideState {n : ℕ} (Ms : ModeSystem A.G n) (l : Fin 4) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (S : ModeSchedule)
    (hA : 6 ≤ S.A0) (SP : SideParams) (c : ℤ × ℤ → Ms.Md → ℂ) (b h : ℤ) :
    ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.basicOut l s mb G j ls h) -
    fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.frozenZ l s mb G j ls (b - 4 * S.K)) +
      fp.physMain Ms.Md (Ms.paperBlockSide S hA SP b (fp.retainedV G b S.K) c)

open Classical in
theorem paper_sideState_budget (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) {ι : Type*} [Fintype ι]
    (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k j : ℕ)
    (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool)) (S : ModeSchedule)
    (hA : 6 ≤ S.A0) (SP : SideParams) (hK : 1 ≤ S.K) {n : ℕ} (Ms : ι → ModeSystem A.G n) (q : ι → ℕ)
    (c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ)
    (Sd : Finset ℕ) (hSd : ∀ t ∈ Sd, t ≤ A.treeDepth) (Ec : ι → ℕ → Finset (ℤ × ℤ))
    (hEc : ∀ G t, ∀ I ∈ Ec G t, I ∈ A.cells ∧ I.1 = A.R.1 + t)
    (hcert : ∀ G t, ∀ I ∈ Ec G t, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (hτN : τ * N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hcc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kk + 1)) :
    ∑ t ∈ Sd, ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.paperSideState (Ms G) l s mb (grp G) j ls (S.withQ0 (q G)) hA SP
          (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
          (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 ≤
      2 * (S.K * (20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
        (1 + Real.log (2 * kk)) ^ 2) + 32) * dyadicGridLength A.G A.R.1) +
      2 * (S.K * ∑ b ∈ Sd.image (fun t => S.K * (t / S.K)), ∑ G,
        ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP (A.R.1 + (b : ℤ)) (fp.retainedV (grp G) (A.R.1 +
            (b : ℤ)) S.K)
          (c G (A.R.1 + (b : ℤ)))‖ ^ 2) := by
  have hroll := fp.rolling_budget l s hT htag d mb hanc hne grp hgrp k j hPH ls hK Sd hSd Ec hEc
    hcert hroot hτ hτ1 hHed hN hτN cc hcc hk hDm hDb hn
  set! V : ι → ℕ → ℝ := fun G b => ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP (A.R.1 + (b : ℤ))
    (fp.retainedV (grp G) (A.R.1 + (b : ℤ)) S.K) (c G (A.R.1 + (b : ℤ)))‖ ^ 2
  have hV := sum_block_le Sd (K := S.K) (by omega) (fun b => ∑ G, V G b)
    (fun b => Finset.sum_nonneg fun G _ => sq_nonneg _)
  -- each term: the rolling part and the side subtotal
  have hterm : ∀ t G, ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
      (fp.paperSideState (Ms G) l s mb (grp G) j ls (S.withQ0 (q G)) hA SP
        (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
        (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 ≤
      2 * ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
          fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K))‖ ^ 2 +
        2 * V G (S.K * (t / S.K)) := by
    intro t G
    set! E := ⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2
    have hE : MeasurableSet E :=
      Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2
    set X := fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
      fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K)
    set! Vb := (Ms G).paperBlockSide (S.withQ0 (q G)) hA SP (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ))
      (fp.retainedV (grp G) (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) S.K)
      (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
    have e : fp.paperSideState (Ms G) l s mb (grp G) j ls (S.withQ0 (q G)) hA SP
        (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
        (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) (A.R.1 + t) =
        fp.physMain (bf.Lab ⊕ Fin fp.Mc) X + fp.physMain (Ms G).Md Vb := by
      unfold paperSideState
      simp only [ModeSchedule.withQ0_K]
      rw [map_sub]
    have h1 : ‖columnL2Restriction E hE (fp.physMain (bf.Lab ⊕ Fin fp.Mc) X)‖ ≤
        ‖columnL2Restriction E hE X‖ := by
      rw [← physEmbed_restrict]; exact norm_physEmbed_apply_le _
    have h2 : ‖columnL2Restriction E hE (fp.physMain (Ms G).Md Vb)‖ ≤ ‖Vb‖ := by
      rw [← physEmbed_restrict]
      refine (norm_physEmbed_apply_le _).trans ?_
      have := columnL2Restriction_norm_sq_le E hE Vb
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    have hV' : V G (S.K * (t / S.K)) = ‖Vb‖ ^ 2 := by
      simp only [V, Vb]
    rw [e, map_add, hV']
    have htri := norm_add_le (columnL2Restriction E hE (fp.physMain (bf.Lab ⊕ Fin fp.Mc) X))
      (columnL2Restriction E hE (fp.physMain (Ms G).Md Vb))
    have ha := norm_nonneg (columnL2Restriction E hE X)
    have hb := norm_nonneg Vb
    nlinarith only [sq_nonneg (‖columnL2Restriction E hE X‖ - ‖Vb‖),
      norm_nonneg (columnL2Restriction E hE (fp.physMain (bf.Lab ⊕ Fin fp.Mc) X) +
        columnL2Restriction E hE (fp.physMain (Ms G).Md Vb)), h1, h2, htri]
  calc _ ≤ ∑ t ∈ Sd, ∑ G, (2 * ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
          fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K))‖ ^ 2 +
        2 * V G (S.K * (t / S.K))) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun G _ => hterm t G
    _ = 2 * ∑ t ∈ Sd, ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
          fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K))‖ ^ 2 +
        2 * ∑ t ∈ Sd, ∑ G, V G (S.K * (t / S.K)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left hroll (by norm_num))
          (mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hV) (by norm_num))
        rfl

open Classical in
theorem paper_sideState_budget_blocks (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) {ι : Type*} [Fintype ι]
    (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k j : ℕ)
    (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool)) (S : ModeSchedule)
    (hA : 6 ≤ S.A0) (SP : SideParams) (hK : 1 ≤ S.K) {n : ℕ} (Ms : ι → ModeSystem A.G n) (q : ι → ℕ)
    (c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ)
    (Sd : Finset ℕ) (hSd : ∀ t ∈ Sd, t ≤ A.treeDepth) (hSdK : ∀ t ∈ Sd, S.K ∣ t)
    (Ec : ι → ℕ → Finset (ℤ × ℤ))
    (hEc : ∀ G t, ∀ I ∈ Ec G t, I ∈ A.cells ∧ I.1 = A.R.1 + t)
    (hcert : ∀ G t, ∀ I ∈ Ec G t, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (hτN : τ * N * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hcc : 1 ≤ cc) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kk + 1)) :
    ∑ t ∈ Sd, ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.paperSideState (Ms G) l s mb (grp G) j ls (S.withQ0 (q G)) hA SP
          (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
          (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 ≤
      2 * ((20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
        (1 + Real.log (2 * kk)) ^ 2) + 32) * dyadicGridLength A.G A.R.1) +
      2 * (∑ b ∈ Sd, ∑ G,
        ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP (A.R.1 + (b : ℤ)) (fp.retainedV (grp G) (A.R.1 +
            (b : ℤ)) S.K)
          (c G (A.R.1 + (b : ℤ)))‖ ^ 2) := by
  have hroll := fp.rolling_budget_blocks l s hT htag d mb hanc hne grp hgrp k j hPH ls hK Sd hSd
    hSdK Ec hEc hcert hroot hτ hτ1 hHed hN hτN cc hcc hk hDm hDb hn
  set! V : ι → ℕ → ℝ := fun G b => ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA SP (A.R.1 + (b : ℤ))
    (fp.retainedV (grp G) (A.R.1 + (b : ℤ)) S.K) (c G (A.R.1 + (b : ℤ)))‖ ^ 2
  -- each term: the rolling part and the side subtotal
  have hterm : ∀ t G, ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
      (fp.paperSideState (Ms G) l s mb (grp G) j ls (S.withQ0 (q G)) hA SP
        (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
        (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) (A.R.1 + t))‖ ^ 2 ≤
      2 * ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
          fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K))‖ ^ 2 +
        2 * V G (S.K * (t / S.K)) := by
    intro t G
    set! E := ⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2
    have hE : MeasurableSet E :=
      Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2
    set X := fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
      fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K)
    set! Vb := (Ms G).paperBlockSide (S.withQ0 (q G)) hA SP (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ))
      (fp.retainedV (grp G) (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) S.K)
      (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
    have e : fp.paperSideState (Ms G) l s mb (grp G) j ls (S.withQ0 (q G)) hA SP
        (c G (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)))
        (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ)) (A.R.1 + t) =
        fp.physMain (bf.Lab ⊕ Fin fp.Mc) X + fp.physMain (Ms G).Md Vb := by
      unfold paperSideState
      simp only [ModeSchedule.withQ0_K]
      rw [map_sub]
    have h1 : ‖columnL2Restriction E hE (fp.physMain (bf.Lab ⊕ Fin fp.Mc) X)‖ ≤
        ‖columnL2Restriction E hE X‖ := by
      rw [← physEmbed_restrict]; exact norm_physEmbed_apply_le _
    have h2 : ‖columnL2Restriction E hE (fp.physMain (Ms G).Md Vb)‖ ≤ ‖Vb‖ := by
      rw [← physEmbed_restrict]
      refine (norm_physEmbed_apply_le _).trans ?_
      have := columnL2Restriction_norm_sq_le E hE Vb
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    have hV' : V G (S.K * (t / S.K)) = ‖Vb‖ ^ 2 := by
      simp only [V, Vb]
    rw [e, map_add, hV']
    have htri := norm_add_le (columnL2Restriction E hE (fp.physMain (bf.Lab ⊕ Fin fp.Mc) X))
      (columnL2Restriction E hE (fp.physMain (Ms G).Md Vb))
    have ha := norm_nonneg (columnL2Restriction E hE X)
    have hb := norm_nonneg Vb
    nlinarith only [sq_nonneg (‖columnL2Restriction E hE X‖ - ‖Vb‖),
      norm_nonneg (columnL2Restriction E hE (fp.physMain (bf.Lab ⊕ Fin fp.Mc) X) +
        columnL2Restriction E hE (fp.physMain (Ms G).Md Vb)), h1, h2, htri]
  calc _ ≤ ∑ t ∈ Sd, ∑ G, (2 * ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
          fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K))‖ ^ 2 +
        2 * V G (S.K * (t / S.K))) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun G _ => hterm t G
    _ = 2 * ∑ t ∈ Sd, ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G t, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t) -
          fp.frozenZ l s mb (grp G) j ls (A.R.1 + ((S.K * (t / S.K) : ℕ) : ℤ) - 4 * S.K))‖ ^ 2 +
        2 * ∑ t ∈ Sd, ∑ G, V G (S.K * (t / S.K)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left hroll (by norm_num)) (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Nat.mul_div_cancel' (hSdK t ht)]


end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)

/-- The state used in the new rolling estimates is exactly the physical side
of the V72 local-form expansion on a basic cell. -/
theorem paperSideAt_eq_restrict_state (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ)
    (hl : D.u ≠ some l) :
    D.paperSideAt l G I =
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.paperSideState (D.Ms l G) l (D.cat l) (D.mbs l) G (D.Lf.role l)
          (D.Lf.layers l) D.S D.hA D.SP (D.c l G (A.blkStart D.S.K I.1))
          (A.blkStart D.S.K I.1) I.1) := by
  simpa only [paperSideState] using D.paperSideAt_basic l G I hl

end SideInput
end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.paper_sideState_budget
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.paper_sideState_budget_blocks
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paperSideAt_eq_restrict_state
