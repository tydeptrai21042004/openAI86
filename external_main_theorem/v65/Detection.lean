import TrilinearHT.Auto.Sec10Detection

/-! The continuous inverse and local detection from the pinned reference,
in the bilinear moment convention of the printed manuscript. These do not
prove the exact external nilmanifold inverse theorem (Theorem 4.7). -/
namespace OpenAI086.ReferenceV65
open Auto MeasureTheory
open scoped ComplexConjugate FourierTransform BigOperators ENNReal

/-- Lemma 4.9, with normalized bilinear correlation on the original interval. -/
theorem continuous_inverse_bilinear :
    ∃ c₀ C : ℕ, 1 ≤ c₀ ∧ 1 ≤ C ∧
      ∀ (a b : ℝ), a < b → ∀ (δ : ℝ), 0 < δ → δ < 1 / 2 →
      ∀ (f : ℝ → ℂ), Measurable f → (∀ x ∈ Set.Ico a b, ‖f x‖ ≤ 1) →
      δ ≤ intervalGowersNorm a b f →
      ∃ (d : ℕ) (A : QuadraticChartData d),
        QuadraticChartComplexity c₀ (Real.exp ((C : ℝ) * (1 + Real.log (1 / δ)) ^ C)) A ∧
        IsBoundedQuadraticChart A ∧
        (Real.exp ((C : ℝ) * (1 + Real.log (1 / δ)) ^ C))⁻¹ ≤
          (b - a)⁻¹ * ‖∫ x in a..b, f x * quadraticChartAtom A x‖  := by
  obtain ⟨c₀, C, hc₀, hC, hinv⟩ := continuous_inverse
  refine ⟨c₀, C, hc₀, hC, ?_⟩
  intro a b hab δ hδ hδ2 f hf hunit hU
  obtain ⟨d, A, hA, hAb, hcorr⟩ := hinv a b hab δ hδ hδ2 f hf hunit hU
  refine ⟨d, conjugateQuadraticChart A, conjugateQuadraticChart_complexity hA,
    conjugateQuadraticChart_bounded hAb, ?_⟩
  simpa only [conjugateQuadraticChart_atom] using hcorr

/-- Lemma 4.12 in arbitrary distinct slots, with a bilinear moment. -/
theorem detection_bilinear (κ : LocalKernelClass) :
    ∃ (c₂ C : ℕ), 1 ≤ c₂ ∧ 1 ≤ C ∧ ∀ q : ℝ, 2 < q → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ {a₀ r C₁ δ : ℝ}, 0 < r → ∀ {w : ℝ × ℝ → ℂ}, IsAdmissibleLocalKernel κ a₀ r w →
    ∀ (f : Fin 4 → ℝ → ℂ), (∀ j, Measurable (f j)) →
    ∀ {jR ih ku lv : Fin 4}, jR ≠ ih → jR ≠ ku → jR ≠ lv → ih ≠ ku → ih ≠ lv → ku ≠ lv →
    1 ≤ C₁ → 0 < δ → δ < 1 / 2 →
    eLpNorm (f jR) 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal C₁ →
    eLpNorm (f ih) (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r) ≤ 1 →
    eLpNorm (f ku) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 →
    eLpNorm (f lv) 2 (normalizedIntervalMeasure a₀ r) ≤ 1 →
    δ < ‖localProgressionForm r w f‖ →
    ∃ (d : ℕ) (Φ : QuadraticChartData d),
      QuadraticChartComplexity c₂
        (Real.exp (Cq * (1 + Real.log C₁ + Real.log (1 / δ)) ^ C)) Φ ∧
      IsBoundedQuadraticChart Φ ∧
      (Real.exp (Cq * (1 + Real.log C₁ + Real.log (1 / δ)) ^ C))⁻¹ ≤
        r⁻¹ * ‖∫ x in a₀..a₀ + r, f jR x * quadraticChartAtom Φ x‖  := by
  obtain ⟨c₂, C, hc₂, hC, hdetect⟩ := detectResidual κ
  refine ⟨c₂, C, hc₂, hC, ?_⟩
  intro q hq
  obtain ⟨Cq, hCq, hdet⟩ := hdetect q hq
  refine ⟨Cq, hCq, ?_⟩
  intro a₀ r C₁ δ hr w hw f hf jR ih ku lv h1 h2 h3 h4 h5 h6 hC₁ hδ hδ2 hR hh hu hv hlarge
  obtain ⟨d, Φ, hΦ, hΦb, hmoment⟩ := hdet hr hw f hf h1 h2 h3 h4 h5 h6
    hC₁ hδ hδ2 hR hh hu hv hlarge
  refine ⟨d, conjugateQuadraticChart Φ, conjugateQuadraticChart_complexity hΦ,
    conjugateQuadraticChart_bounded hΦb, ?_⟩
  simpa only [conjugateQuadraticChart_atom] using hmoment

end OpenAI086.ReferenceV65
#print axioms OpenAI086.ReferenceV65.continuous_inverse_bilinear
#print axioms OpenAI086.ReferenceV65.detection_bilinear
