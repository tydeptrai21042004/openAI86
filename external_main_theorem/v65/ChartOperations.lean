import TrilinearHT.Auto.Sec09_2ChartFourierSeparation

/-! Source-fidelity adapters for Definition 4.1 and Lemmas 4.2, 4.4.
The analytic chart machinery comes from the pinned Roos/Claude reference.
The statements below combine its actual chart operations, not finite proxies. -/
namespace OpenAI086.ReferenceV65
open Auto MeasureTheory
open scoped ComplexConjugate FourierTransform BigOperators

/-- Two different affine changes followed by a conjugated product, with
one budget independent of all four affine parameters. -/
theorem affine_conjugate_product {d e c : ℕ} {H : ℝ}
    (A : QuadraticChartData d) (B : QuadraticChartData e)
    (hA : QuadraticChartComplexity c H A) (hB : QuadraticChartComplexity c H B)
    (hc : 1 ≤ c) (s t u v : ℝ) :
    ∃ C : QuadraticChartData (d + e),
      QuadraticChartComplexity c (chartTranslationBudget H ^ 6) C ∧
      (IsBoundedQuadraticChart A → IsBoundedQuadraticChart B → IsBoundedQuadraticChart C) ∧
      ∀ y, quadraticChartAtom C y = quadraticChartAtom A (s*y+t) *
        star (quadraticChartAtom B (u*y+v)) := by
  obtain ⟨A', hA', hAb, hAe⟩ := quadraticChart_affine_closure hA hc s t
  obtain ⟨B', hB', hBb, hBe⟩ := quadraticChart_affine_closure hB hc u v
  refine ⟨productQuadraticChart A' (conjugateQuadraticChart B'),
    productQuadraticChart_complexity hA' (conjugateQuadraticChart_complexity hB') hc,
    ?_, ?_⟩
  · intro ha hb
    exact productQuadraticChart_bounded (hAb ha) (conjugateQuadraticChart_bounded (hBb hb))
  · intro y
    rw [productQuadraticChart_atom, conjugateQuadraticChart_atom, hAe, hBe]

/-- Restore the effective quadratic and linear phase in (3) from a
phase-removed Fourier expansion. The result is a literal HasSum, not a
formal manipulation of an infinite series. -/
theorem restore_chart_phase {ι : Type*} (a : ι → ℂ) (ω : ι → ℝ)
    (p : ℝ) (Q : ℂ)
    (h : HasSum (fun i => a i * (Real.fourierChar (ω i) : ℂ))
      ((Real.fourierChar (-p) : ℂ) * Q)) :
    HasSum (fun i => a i * (Real.fourierChar (p + ω i) : ℂ)) Q := by
  have hm := h.mul_left (Real.fourierChar p : ℂ)
  convert hm using 1
  · funext i
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

/-- The zero-dimensional charts already include every linear character;
there is no cost in the unrestricted frequency. -/
theorem linear_chart (c : ℕ) {H : ℝ} (hH : Real.exp 2 ≤ H) (β : ℝ) :
    ∃ A : QuadraticChartData 0, QuadraticChartComplexity c H A ∧
      IsBoundedQuadraticChart A ∧
      ∀ y, quadraticChartAtom A y = (Real.fourierChar (β*y) : ℂ) := by
  refine ⟨ordinaryQuadraticChart 0 β, ordinaryQuadraticChart_complexity c hH 0 β,
    ordinaryQuadraticChart_bounded 0 β, ?_⟩
  intro y
  simp [ordinaryQuadraticChart_atom]

end OpenAI086.ReferenceV65
#print axioms OpenAI086.ReferenceV65.affine_conjugate_product
#print axioms OpenAI086.ReferenceV65.restore_chart_phase
#print axioms OpenAI086.ReferenceV65.linear_chart
