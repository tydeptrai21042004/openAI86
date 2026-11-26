import TrilinearHT.Auto.Sec16_2QuantitativeInequality

/-! V63: connect the actual reference leaf estimate to its polynomial
coefficient budgets, at the reference parameter choices δs=1/1024, J=3,
Aw=1. The error sum is not raised to a fractional power. The printed
paper's distinct geometric data and the parameter comparison remain open. -/
namespace OpenAI086.ReferenceV63
open Auto MeasureTheory Metric
open scoped BigOperators ENNReal FourierTransform ComplexConjugate
noncomputable section
open Classical

variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams} (D : fp.SideInput)

theorem core_coefficient_budget (hSP : D.SP = D.S.sideParams (1 / 1024)) (Iw : ℕ)
    {B L U ε K IB : ℝ} (hB : 2 ≤ B)
    (hd : (D.S.dmax : ℝ) + 5 ≤ B) (hD1 : 1 ≤ D.S.Dstar) (hH1 : 1 ≤ D.S.H)
    (hD : Real.log D.S.Dstar ≤ B) (hH : Real.log D.S.H ≤ B)
    (hJ : (D.S.Jstar : ℝ) + 1 ≤ B)
    (hL0 : 0 ≤ Real.logb 2 (U / ε) + 1) (hL : Real.logb 2 (U / ε) + 1 ≤ L)
    (hK : 1 ≤ K) (hI : (Iw : ℝ) + 1 ≤ IB) :
    D.coreM4 3 U ε K + ∑ l : Fin 4, D.coreM3 3 1 Iw U ε K l ≤
      C4c κ' * B ^ 30 * L ^ 4 * K ^ 2 + 4 * (C3c κ' * B ^ 30 * IB * L ^ 4 * K ^ 2) := by
  have h4 := coreM4F_le κ' D.S (U := U) (ε := ε) (Kc := K) hB hd hD1 hH1 hD hH hJ hL0 hL hK
  have h3 : ∀ l : Fin 4, D.coreM3 3 1 Iw U ε K l ≤
      C3c κ' * B ^ 30 * IB * L ^ 4 * K ^ 2 := by
    intro l
    rw [D.coreM3_eq_F hSP]
    exact coreM3F_le κ' D.S Iw l hB hd hD1 hH1 hD hH hJ hL0 hL hK hI
  rw [D.coreM4_eq_F hSP]
  apply add_le_add h4
  calc
    _ ≤ ∑ _l : Fin 4, C3c κ' * B ^ 30 * IB * L ^ 4 * K ^ 2 :=
      Finset.sum_le_sum fun l _ => h3 l
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- Actual reference cell minimum with explicit schedule coefficient and absolute error budget. -/
theorem leaf_core_polynomial {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (qG : bf.Grp → ℕ) (hqG : ∀ G, 1 ≤ qG G ∧ qG G ≤ D.S.Q0)
    (J : ℕ) (hJ3 : 3 ≤ J) (Aw Iw : ℕ) (hAw : 1 ≤ Aw) (hIw1 : D.U0 ≤ 2 ^ (Iw + 1))
    (hIw2 : (2 : ℝ) ^ Iw ≤ 2 * D.U0) (T : Finset (ℤ × ℤ)) (hTc : T ⊆ A.cells)
    (hTR : ∀ I ∈ T, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (gset : Finset bf.Grp) (hgs : ∀ I ∈ T, gs I ⊆ gset)
    (huse : ∀ I ∈ T, ∀ G ∈ gs I, fp.ActualUse G I) (z : bf.Grp → ChartTag)
    (hGc : ∀ G ∈ gset, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (δ Cm : bf.Grp → ℝ) (Kt Kf : ℕ)
    (hprin : ∀ G ∈ gset, (D.withQ0 (qG G)).PrinOK G (δ G) (Cm G) Kt Kf)
    (hstab : ∀ G ∈ gset, (D.withQ0 (qG G)).Stab) (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K)
    (hJ : 2 ≤ D.SP.Jst) (hδs : 0 < D.SP.δs) (hδ16 : D.SP.δs ≤ 1 / 16)
    (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst) (hq : 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) < 1)
    (hcard : ∀ I ∈ T, ∀ G ∈ gset, ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (Rr : ∀ (j : Fin 4) (h : ℕ) (_ : ℕ × ℕ) (G : {G // G ∈ gset}),
      (D.Ms j G.1).RepClass (D.withQ0 (qG G.1)).S D.hA D.SP 10 h)
    (Bs : Finset ℤ) (hNdR : ∀ j, ∀ h ≤ D.SP.Jst, ∀ t (G : {G // G ∈ gset}) c,
      c ∈ (D.Ms j G.1).succNodes (D.withQ0 (qG G.1)).S D.hA D.SP
        (fp.retainedPairs G.1 Bs D.S.K) h →
      (D.Ms j G.1).nodeType1 (D.withQ0 (qG G.1)).S D.hA 10 h c = t.1 →
      (D.Ms j G.1).nodeType2 (D.withQ0 (qG G.1)).S D.hA 10 h c = t.2 → c ∈ (Rr j h t G).Nd)
    (hTB : ∀ I ∈ T, A.blkStart D.S.K I.1 ∈ Bs) (Cut : Fin 4 → Finset (ℤ × ℤ))
    (hTcut : ∀ I ∈ T, ∀ j, ∀ e ∈ Cut j,
      ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)
    (Thr : Finset ℝ) {ε U Mt Ks : ℝ} (hε : 0 < ε) (hεU : ε ≤ U)
    (hThr : ∀ σ, ε ≤ σ → σ ≤ U → (∃ k : ℤ, σ = (2 : ℝ) ^ k) → D.S.Dstar⁻¹ ≤ σ → σ ∈ Thr)
    (hTop : ∀ j y, ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
      ∀ t ∈ Finset.range (Nat.log 2 ⌊D.S.Dstar⌋₊ + 1) ×ˢ
        Finset.range (Nat.log 2 ⌊D.S.Dstar⌋₊ + 1), ∀ σ ∈ Thr,
      (∑ G : {G // G ∈ gset}, (((fp.useInst G.1 D.S.K (Rr j h t G).Nd).filter fun p =>
          (∀ e ∈ Cut j, ¬ dyadicGridCell A.G p.1.1 p.1.2 ⊆ dyadicGridCell A.G e.1 e.2) ∧
          y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
            σ ^ 2 ≤ (D.Ms j G.1).nodeSize (D.withQ0 (qG G.1)).S D.hA D.SP (D.c j G.1) h p).image
          fun p => (Rr j h t G).rep p.2).card : ℝ) ≤ Mt * σ ^ (-2 : ℝ))
    (hpathD : ∀ j y, (∑ G : {G // G ∈ gset}, ((D.Ms j G.1).ptSet y).card : ℝ) ≤ D.S.Dstar)
    (hU : ∀ I ∈ T, ∀ G ∈ gs I, ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ j,
      ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h, (D.withQ0 (qG G)).clsSize G I j F ≤ U)
    (hUs : ∀ l, ∀ I ∈ T, ∀ G ∈ gs I, Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ *
      ∫ y in (dyadicGridLeft A.G I.1 I.2)..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys ((D.withQ0 (qG G)).toLeaf.sv l G I) y‖ ^ 2) ≤ U)
    (hside : ∀ y, ∑ I ∈ T with y ∈ dyadicGridCell A.G I.1 I.2, ∑ G ∈ gs I,
      (D.toLeafQ qG).s2 G I ≤ Ks)
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md) {η : ℝ} (hη : 0 ≤ η)
    (hδfixed : δs = 1 / 1024) (hJfixed : J = 3) (hAwfixed : Aw = 1)
    {B Lb IB E : ℝ} (hB2 : 2 ≤ B) (hdb : (D.S.dmax : ℝ) + 5 ≤ B)
    (hH1 : 1 ≤ D.S.H) (hDb : Real.log D.S.Dstar ≤ B) (hHb : Real.log D.S.H ≤ B)
    (hJb : (D.S.Jstar : ℝ) + 1 ≤ B)
    (hL0 : 0 ≤ Real.logb 2 (U / ε) + 1) (hLb : Real.logb 2 (U / ε) + 1 ≤ Lb)
    (hIb : (Iw : ℝ) + 1 ≤ IB)
    (hE : ∑ I ∈ T, dyadicGridLength A.G I.1 * D.coreE qG gs J Aw Iw U ε I ≤ E) :
    ∑ I ∈ T, dyadicGridLength A.G I.1 * min η ‖∑ τ ∈ Finset.univ.filter
        (fun τ : Fin 4 → Fin 3 => (∀ l, τ l ≠ 2) ∧ 3 ≤ patternCount τ 0),
        ∑ G ∈ gs I, fp.Λc I (patternPiece (fun l => (D.withQ0 (qG G)).coreAt l G I)
          (fun l => (D.toLeafQ qG).sv l G I) (fun l => (D.withQ0 (qG G)).errAt L l G I) τ)‖ ≤
      η ^ (1 / 1200 : ℝ) * (dyadicGridLength A.G A.R.1 *
        (C4c κ' * B ^ 30 * Lb ^ 4 * (max (max 1 Mt) Ks) ^ 2 +
          4 * (C3c κ' * B ^ 30 * IB * Lb ^ 4 * (max (max 1 Mt) Ks) ^ 2))) + E := by
  have h := D.leaf_core_estimate hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG J hJ3 Aw Iw hAw hIw1
    hIw2 T hTc hTR gs gset hgs huse z hGc δ Cm Kt Kf hprin hstab hK hJ hδs hδ16 hδJ hq
    hcard Rr Bs hNdR hTB Cut hTcut Thr hε hεU hThr hTop hpathD hU hUs hside L hη
  have hKc : 1 ≤ max (max 1 Mt) Ks := (le_max_left _ _).trans (le_max_left _ _)
  have hSPfixed : D.SP = D.S.sideParams (1 / 1024) := by simpa only [hδfixed] using hSP
  have hb := core_coefficient_budget D hSPfixed Iw hB2 hdb (by linarith : 1 ≤ D.S.Dstar)
    hH1 hDb hHb hJb hL0 hLb hKc hIb
  have hb' : D.coreM4 J U ε (max (max 1 Mt) Ks) +
      ∑ l, D.coreM3 J Aw Iw U ε (max (max 1 Mt) Ks) l ≤
      C4c κ' * B ^ 30 * Lb ^ 4 * (max (max 1 Mt) Ks) ^ 2 +
        4 * (C3c κ' * B ^ 30 * IB * Lb ^ 4 * (max (max 1 Mt) Ks) ^ 2) := by
    simpa only [hJfixed, hAwfixed] using hb
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hb' (dyadicGridLength_pos A.G A.R.1).le)
    (Real.rpow_nonneg hη _)) hE)

end
end OpenAI086.ReferenceV63
#print axioms OpenAI086.ReferenceV63.core_coefficient_budget
#print axioms OpenAI086.ReferenceV63.leaf_core_polynomial
