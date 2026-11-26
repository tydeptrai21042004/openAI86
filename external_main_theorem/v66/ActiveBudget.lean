import TrilinearHT.Auto.Sec12_4BinaryLocalizationVariation

/-! Sections 5.5 and 6.5: the active count, weighted length, and base error
are estimates for the SAME ActiveSetup. The root length is not an additional
assumption. Reference: Roos/Claude, Apache-2.0. -/
namespace OpenAI086.ReferenceV66
open Auto MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] Auto.ActiveSetup.fin

noncomputable def activePathBudget {κ : LocalKernelClass} {c₀ : ℕ}
    (A : ActiveSetup κ c₀) (δ : ℝ) (C : ℕ) : ℝ :=
  4 * Fintype.card A.L ^ 3 * (C * (216 * Real.log (chartTranslationBudget A.H) +
    Real.log (sliceConst κ) + 2 * Real.log δ⁻¹) ^ C)

/-- The active-path bound also controls the sum of lengths of EVERY subset
of active cells, so a numerical error uniform in the cell is summable. -/
theorem active_subset_length {κ : LocalKernelClass} {c₀ : ℕ}
    (A : ActiveSetup κ c₀) (δ M : ℝ) (cs : Finset (ℤ × ℤ))
    (hcs : cs ⊆ A.cells.filter (A.active δ))
    (hM : ∀ y : ℝ,
      ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active δ I).card : ℝ) ≤ M) :
    ∑ I ∈ cs, dyadicGridLength A.G I.1 ≤ dyadicGridLength A.G A.R.1 * M := by
  classical
  have hsub : ∀ I ∈ cs, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G A.R.1 A.R.2 := fun I hI => A.sub I (Finset.mem_filter.mp (hcs hI)).1
  have hpath : ∀ y : ℝ, ∑ I ∈ cs with y ∈ dyadicGridCell A.G I.1 I.2, (1 : ℝ) ≤ M := by
    intro y
    have hs : (cs.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2) ⊆
        A.cells.filter (fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active δ I) := by
      intro I hI
      obtain ⟨hIc, hy⟩ := Finset.mem_filter.mp hI
      obtain ⟨hIa, ha⟩ := Finset.mem_filter.mp (hcs hIc)
      exact Finset.mem_filter.mpr ⟨hIa, hy, ha⟩
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact (show ((cs.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2).card : ℝ) ≤ _ from
      by exact_mod_cast Finset.card_le_card hs).trans (hM y)
  simpa only [mul_one] using cells_sum_le_of_path A.G A.R cs hsub
    (f := fun _ => (1 : ℝ)) (fun _ => zero_le_one) hpath

/-- Joint form of the active-cell reduction, its path bound, and its packing
bound. Constants for the inactive error and count need not coincide. -/
theorem base_reduction_joint (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (Ccount Ctail : ℕ) (Cr : ℝ), 1 ≤ Ccount ∧ 0 ≤ Cr ∧
    ∀ (A : ActiveSetup κ c₀) (δ : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ A.η →
      (∀ y : ℝ, ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧
        A.active δ I).card : ℝ) ≤ activePathBudget A δ Ccount) ∧
      (∀ cs : Finset (ℤ × ℤ), cs ⊆ A.cells.filter (A.active δ) →
        ∑ I ∈ cs, dyadicGridLength A.G I.1 ≤
          dyadicGridLength A.G A.R.1 * activePathBudget A δ Ccount) ∧
      (∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.Y I)‖) ≤
        ∑ p : Fin 3, ∑ I ∈ A.cells with A.active δ I,
            dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ +
          ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.z 3 I)‖ +
          3 * Fintype.card A.L ^ 3 * (A.Dc ^ 3 * (A.S + Fintype.card A.L * A.Dc)) *
            (dyadicGridLength A.G A.R.1 *
              (δ * Cr * (Real.log (chartTranslationBudget A.H) + Real.log δ⁻¹ + 1) ^ Ctail)) := by
  obtain ⟨Ccount, hC, hcount⟩ := ActiveSetup.active_count κ c₀ hc
  obtain ⟨Ctail, Cr, hCr, hred⟩ := ActiveSetup.reduction κ c₀ hc
  refine ⟨Ccount, Ctail, Cr, hC, hCr, ?_⟩
  intro A δ hδ hδ1 hη
  have hm : ∀ y : ℝ, ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧
      A.active δ I).card : ℝ) ≤ activePathBudget A δ Ccount := by
    intro y
    simpa only [activePathBudget] using hcount A δ hδ hδ1 y
  exact ⟨hm, fun cs hcs => active_subset_length A δ _ cs hcs hm, hred A δ hδ hδ1 hη⟩

/-- Numerical error in Proposition 6.8, after summing the actual active cells
and the guarded-search leaves. It uses the original reference leaf error
rather than assuming a bound on the total length. -/
theorem localization_error_budget {κ : LocalKernelClass} {c₀ : ℕ}
    (A : ActiveSetup κ c₀) (δ M : ℝ) (cs : Finset (ℤ × ℤ))
    (hcs : cs ⊆ A.cells.filter (A.active δ))
    (hM : ∀ y : ℝ, ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧
      A.active δ I).card : ℝ) ≤ M)
    (fuel Lc : ℕ) (up₀ : Fin 4) {e ε : ℝ} (he : 0 ≤ e)
    (hε : M * (2 : ℝ)^fuel * e ≤ ε) :
    (∑ I ∈ cs, dyadicGridLength A.G I.1) *
      ((searchList fuel Lc up₀).length * e) ≤
        dyadicGridLength A.G A.R.1 * ε := by
  have hlength := active_subset_length A δ M cs hcs hM
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans (hM 0)
  have hleaf : ((searchList fuel Lc up₀).length : ℝ) ≤ (2 : ℝ)^fuel := by
    exact_mod_cast (show (searchList fuel Lc up₀).length ≤ 2 ^ fuel from
      searchLeaves_length_le fuel 1 Lc up₀ none (fun _ => []))
  have hr := (dyadicGridLength_pos A.G A.R.1).le
  calc _ ≤ (dyadicGridLength A.G A.R.1 * M) *
      ((searchList fuel Lc up₀).length * e) :=
        mul_le_mul_of_nonneg_right hlength (mul_nonneg (Nat.cast_nonneg _) he)
    _ ≤ (dyadicGridLength A.G A.R.1 * M) * ((2 : ℝ)^fuel * e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hleaf he) (mul_nonneg hr hM0)
    _ = dyadicGridLength A.G A.R.1 * (M * (2 : ℝ)^fuel * e) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hε hr

end OpenAI086.ReferenceV66
#print axioms OpenAI086.ReferenceV66.active_subset_length
#print axioms OpenAI086.ReferenceV66.base_reduction_joint
#print axioms OpenAI086.ReferenceV66.localization_error_budget
