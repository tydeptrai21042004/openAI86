import TrilinearHT.Auto.Sec11_1aPredictors

/-! Corollary 5.2: remove the dimension restriction in the reference predictor
construction. The package is over padded charts, with literal pointwise
identities to the original low inputs. No change of the local forms is made.
Based on the pinned Roos/Claude reference (Apache-2.0). -/
namespace OpenAI086.ReferenceV66
open Auto MeasureTheory
open scoped ComplexConjugate FourierTransform BigOperators ENNReal

/-- All-dimensional finite predictor package with a single common budget. -/
theorem predictors_all_dimensions (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ (c₁ C : ℕ) (W₀ : ℝ), 1 ≤ c₁ ∧ Real.exp 2 ≤ W₀ ∧
    ∀ {d e : ℕ} (H B : ℝ) (A : QuadraticChartData d) (A' : QuadraticChartData e),
      QuadraticChartComplexity c₀ H A → QuadraticChartComplexity c₀ H A' →
      IsBoundedQuadraticChart A → IsBoundedQuadraticChart A' → 1 ≤ B →
      ∀ {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
      ∃ (P : QuadraticChartData (d + 1)) (Q : QuadraticChartData (e + 1)),
        (∀ y, quadraticChartAtom P y = quadraticChartAtom A y) ∧
        (∀ y, quadraticChartAtom Q y = quadraticChartAtom A' y) ∧
        Nonempty (PredictorPackage κ P Q a i k b B
          (Real.exp (C * (1 + B + Real.log (max H W₀ ^ 6)) ^ C)) c₁) := by
  obtain ⟨cp, W₀, hcp, hW₀, hpad⟩ := exists_pad_chart
  obtain ⟨c₁, C, hc₁, hpred⟩ := predictorPackage_nonempty (max c₀ cp)
    (le_trans hc (le_max_left _ _)) κ
  refine ⟨c₁, C, W₀, hc₁, hW₀, ?_⟩
  intro d e H B A A' hA hA' hAb hA'b hB a i k b h1 h2 h3 h4 h5 h6
  obtain ⟨P, hP, hPc, hPb⟩ := hpad A hA hc
  obtain ⟨Q, hQ, hQc, hQb⟩ := hpad A' hA' hc
  exact ⟨P, Q, hP, hQ, hpred (max H W₀ ^ 6) B P Q (by omega) (by omega)
    hPc hQc (hPb hAb) (hQb hA'b) hB h1 h2 h3 h4 h5 h6⟩

end OpenAI086.ReferenceV66
#print axioms OpenAI086.ReferenceV66.predictors_all_dimensions
