import TrilinearHT.Auto.Sec16_3SummingUpdateLevels

/-! V61. Conditional outer reduction on the pinned reference model.
These declarations do not invoke the already finished main theorem to
prove an intermediate lemma. The normalized estimate is the premise. -/
namespace OpenAI086.ReferenceV61
open Auto MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-- First implication in Lemma 2.4. Preserve the paper's strict q>2 and
choose the small coefficient only after q has been selected. -/
theorem outer_uniform
    (hnorm : ∀ κ : LocalKernelClass, ∃ q : ℝ, 2 < q ∧ q < 3 ∧
      ∀ c : ℝ, 0 < c → ∃ A : ℝ, 0 ≤ A ∧ ∀ N, NormalizedAbsorption κ q N A c) :
    ∀ κ : LocalKernelClass, ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∃ Cst : ℝ,
      ∀ N, finiteDepthConstant κ q N ≤ Cst := by
  intro κ
  obtain ⟨q, hq2, hq3, h⟩ := hnorm κ
  have hK : 0 < 4 / 3 * (16 : ℝ) ^ (4 / q) := by positivity
  obtain ⟨A, hA, hN⟩ := h (1 / 2 / (4 / 3 * (16 : ℝ) ^ (4 / q))) (by positivity)
  refine ⟨q, hq2, hq3, _, uniform_local_of_normalized κ hq2.le hA (by positivity) ?_ hN⟩
  rw [mul_div_cancel₀ _ hK.ne']

/-- The second implication is replayed on the reference's full theorem
(including principal value and unique extension). The explicit conclusion is
exactly the result of applying the upstream conditional theorem. -/
theorem outer_main
    (huni : ∀ κ : LocalKernelClass, ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∃ Cst : ℝ,
      ∀ N, finiteDepthConstant κ q N ≤ Cst) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ,
        (∀ x, Filter.Tendsto (TrilinearHT.T_trunc ![⇑f₁, ⇑f₂, ⇑f₃] x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃] x))) ∧
        MemLp (TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) 1 volume ∧
        ∫⁻ x, ‖TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃] x‖ₑ ≤
          ENNReal.ofReal C * (eLpNorm f₁ 3 volume * eLpNorm f₂ 3 volume * eLpNorm f₃ 3 volume)) ∧
      ∃ T' : Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 3 (volume : Measure ℝ) →L[ℂ]
          Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ),
        (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ, ⇑(T' (f₁.toLp 3 (volume : Measure ℝ))
          (f₂.toLp 3 (volume : Measure ℝ)) (f₃.toLp 3 (volume : Measure ℝ))) =ᵐ[volume]
            TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) ∧
        (∀ x y z, ‖T' x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) ∧
        ∀ S : Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 3 (volume : Measure ℝ) →L[ℂ]
            Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ),
          (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ, ⇑(S (f₁.toLp 3 (volume : Measure ℝ))
            (f₂.toLp 3 (volume : Measure ℝ)) (f₃.toLp 3 (volume : Measure ℝ))) =ᵐ[volume]
              TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) → S = T' :=
  tht_main_of_uniform (fun κ => by
    obtain ⟨q, hq2, hq3, Cst, hC⟩ := huni κ
    exact ⟨q, hq2.le, hq3, Cst, hC⟩)

end OpenAI086.ReferenceV61

#print axioms OpenAI086.ReferenceV61.outer_uniform
#print axioms OpenAI086.ReferenceV61.outer_main
#print axioms Auto.uniform_local_of_normalized
#print axioms Auto.tht_main_of_uniform
#print axioms Auto.continuous_inverse
#print axioms Auto.activeCellReduction
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.attempt_localization
#print axioms Auto.exceptional_blocks_count
#print axioms Auto.rational_span_expand_bounded
#print axioms Auto.height_stabilization
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.linear_energy
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.leaf_core_estimate
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.four_core_final_side
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.three_core_final_side
#print axioms Auto.core_final_patterns
