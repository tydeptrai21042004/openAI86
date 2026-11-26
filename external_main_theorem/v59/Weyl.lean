import TrilinearHT.Auto.Sec09_1ReturnWeylSplitting

/-! Lemma 4.3: retain the actual chart, rational matrix heights, isotropic
subspace, and quantitative operator norms. Uses the reference's concrete
analytic and lattice proof; not an independent reproduction of it. -/
namespace OpenAI086.ReferenceV59
open Auto MeasureTheory
open scoped FourierTransform Matrix BigOperators

theorem lemma43 (c₀ : ℕ) (hc : 1 ≤ c₀) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ {d k : ℕ}, 1 ≤ k → k ≤ 3 →
      ∀ (H : ℝ) (A : MultivariableQuadraticChartData k d),
      MultivariableQuadraticChartComplexity c₀ H A →
      ∀ (θ : (Fin k → ℝ) → ℂ), Measurable θ → (∀ z, ‖θ z‖ ≤ H) →
      (∀ x y, ‖θ y - θ x‖ ≤ H * ‖y - x‖) → (∀ z, θ z ≠ 0 → ∀ i, |z i| ≤ R) →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      (∀ t < δ, ∃ ξ : EuclideanSpace ℝ (Fin k), t < ‖𝓕 (fun z : EuclideanSpace ℝ (Fin k) =>
        θ z.ofLp * multivariableQuadraticChartAtom A z.ofLp) ξ‖) →
      let B := Real.exp ((D : ℝ) * (1 + Real.log H + Real.log δ⁻¹) ^ D)
      ∃ (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (Q : Matrix (Fin d) (Fin d) ℚ),
        realMatrixOperator (Q.map (fun q => (q : ℝ))) = Uᗮ.starProjection ∧
        realMatrixOperator ((1 - Q).map (fun q => (q : ℝ))) = U.starProjection ∧
        (∀ x ∈ U, ∀ y ∈ U, inner ℝ y
          (realMatrixOperator ((A.matrix.map (fun q => (q : ℝ))) -
            (A.matrix.map (fun q => (q : ℝ))).transpose) x) = 0) ∧
        (∀ i j, (rationalHeight (Q i j) : ℝ) ≤ B) ∧
        (∀ i j, (rationalHeight ((1 - Q) i j) : ℝ) ≤ B) ∧
        ‖realMatrixOperator (Q.map (fun q => (q : ℝ)) * A.horizontal)‖ ≤ B ∧
        ‖realMatrixOperator (effectiveReturnQuadratic (A.matrix.map (fun q => (q : ℝ)))
          A.quadratic A.horizontal ((1 - Q).map (fun q => (q : ℝ)) * A.horizontal)
          (Q.map (fun q => (q : ℝ)) * A.horizontal))‖ ≤ B := by
  obtain ⟨D, hD, h⟩ := Auto.weylSplitting c₀ hc R hR
  refine ⟨D, hD, ?_⟩
  intro d k hk1 hk3 H A hA θ hθm hθ hθLip hθsupp δ hδ hδhalf hsup
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr (by linarith)
  simpa only [max_eq_right hi] using h hk1 hk3 H A hA θ hθm hθ hθLip hθsupp δ hδ hsup

end OpenAI086.ReferenceV59
#print axioms OpenAI086.ReferenceV59.lemma43
