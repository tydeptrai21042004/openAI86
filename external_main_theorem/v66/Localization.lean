import ReferenceV66ActiveBudget

/-! Proposition 6.8 on the reference's actual catalogs, guards and current
ball filters. Strengthen the conclusion with the active-cell packing bound.
The reference's geometric and catalog hypotheses are retained verbatim.
Adapted from Roos/Claude, Apache-2.0 (Sec12_4BinaryLocalizationVariation). -/
namespace OpenAI086.ReferenceV66
open Auto MeasureTheory
open scoped Classical FourierTransform ComplexConjugate BigOperators ENNReal
attribute [local instance] Auto.ActiveSetup.fin
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

theorem attempt_localization_budgeted (Tc : Finset (ℤ × ℤ)) (hTc : Tc ⊆ A.cells) {Dst : ℕ}
    (hst : SameTagBound κ A.csrc Dst)
    (x : ℤ × ℤ → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (hxb : ∀ l, ∀ I ∈ Tc, MainFresh fp.Mc 0 (x I l) ∧
      ∀ᵐ y ∂volume, y ∉ dyadicGridCell A.G I.1 I.2 →
        (x I l : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y = 0)
    {Kt : ℕ} (hKt : ∀ I, Fintype.card (fp.TestName I Unit) ≤ Kt) {Mp : ℕ} (hMp : 1 ≤ Mp)
    {τ₃ : ℝ} (hτ₃ : 0 < τ₃) (hτ₃1 : τ₃ ≤ 1) {Tmax : ℕ} (n : ℕ → ℝ)
    (hn0 : 2 * A.colBudget ≤ n 0)
    (hratio : ∀ r, (1 + (fp.Lc + 6) * Mp * closureRatio A.famVtxBound Kt fp.mH Tmax
      (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃) * n r ≤ n (r + 1))
    (hT : n (fp.Lc + 5) ≤ Tmax) (hMc : Tc.card * Tmax ≤ fp.Mc)
    {fuel : ℕ} {up₀ : Fin 4} (hL1 : 1 ≤ fp.Lc) (hfuel : fp.Lc - 1 < 2 ^ fuel)
    (hmH : fuel ≤ fp.mH)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc +
      Real.log (τ₃ / ((A.famVtxBound : ℝ) ^ 2 * n (fp.Lc + 1)))⁻¹) ^ A.Dg) ≤ fp.Hed)
    (d : bf.Vtx) :
    ∃ cat : Fin 4 → List (CatCol bf.Vtx),
      (∀ l, (∀ I ∈ Tc, ∀ w : fp.TestName I Unit, (fp.testOf l I (fun _ : Unit => x I l) w).Pass
          A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I)
            (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun _ : Unit => x I l) w).r) fp.mH
              (cat l)) ∧
        (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤ fp.Lc + 5 ∧
          ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
            e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧
        (∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1) ∧
        (∀ I, (Tc.filter fun I' : ℤ × ℤ =>
            dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I'.1 I'.2).card ≤ Mp →
          ∀ r ≤ fp.Lc + 5, ((mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧
        (cat l).length ≤ Tc.card * Tmax) ∧
      ∀ cs ⊆ Tc, (∀ I ∈ cs, (Tc.filter fun I' : ℤ × ℤ =>
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I'.1 I'.2).card ≤ Mp) →
        (∀ I ∈ cs, ∀ w ∈ bf.admT.X (bf.admAt I),
          fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) w)) →
        (∀ I ∈ cs, ∀ w ∈ bf.admT.X (bf.admAt I),
          fp.K.color bf.admT A.famVtxBound (bf.admAt I) w ≤ fp.Lc) →
        (∀ I ∈ cs, ∃ cb : bf.Lab → ℂ, x I up₀ = ∑ v ∈ Finset.univ.filter
          (fun v => (bf.origCols up₀).avail I v), cb v •
            mainCol A.G fp.Mc (bf.origCols up₀) [] I (Sum.inl v)) →
        ∀ {Sz η : ℝ}, 0 ≤ η → 0 < Sz →
        (∀ I ∈ cs, ∀ l, ‖x I l‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz) →
        ∀ (δ M ε : ℝ), (cs ⊆ A.cells.filter (A.active δ)) →
        (∀ y : ℝ, ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧
          A.active δ I).card : ℝ) ≤ M) →
        M * (2 : ℝ)^fuel * (9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * Sz ^ 4) ≤ ε →
        ∑ I ∈ cs, dyadicGridLength A.G I.1 * min η ‖fp.Λc I (x I)‖ ≤
          ∑ s ∈ Finset.range (searchList fuel fp.Lc up₀).length, ∑ I ∈ cs,
              dyadicGridLength A.G I.1 * min η ‖∑ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
                fp.Λc I (fun l => fp.ballFilt l (cat l) I G ((leafAt fuel fp.Lc up₀ s).role l)
                  (fp.inputL cat I (x I) (leafAt fuel fp.Lc up₀ s).layers l))‖ +
            dyadicGridLength A.G A.R.1 * ε := by
  classical
  obtain ⟨cat, hcat, hloc⟩ := fp.attempt_localization Tc hTc hst x hxb hKt hMp hτ₃ hτ₃1 n
    hn0 hratio hT hMc hL1 hfuel hmH hHed d
  refine ⟨cat, hcat, ?_⟩
  intro cs hcs hmult hsucc hLcol hbasic Sz η hη hSz0 hSz δ M ε ha hM he
  have h := hloc cs hcs hmult hsucc hLcol hbasic hη hSz0 hSz
  have hE := localization_error_budget A δ M cs ha hM fuel fp.Lc up₀
    (e := 9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * Sz ^ 4) (by positivity) he
  exact h.trans (add_le_add_left hE _)

end OpenAI086.ReferenceV66
#print axioms OpenAI086.ReferenceV66.attempt_localization_budgeted
