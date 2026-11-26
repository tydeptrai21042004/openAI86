import TrilinearHT.Auto.Sec16_3SummingUpdateLevels

/-! Exact quantifier order of paper Proposition 2.3 and strict q in
Theorem 2.2 on the reference's concrete admissible-kernel data.
This uses the attributed pinned reference proof, not an independent proof. -/
namespace OpenAI086.ReferenceV60
open Auto

theorem proposition23 (κ : LocalKernelClass) :
    ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∀ c : ℝ, 0 < c → ∃ A : ℝ, 0 ≤ A ∧
      ∀ N, NormalizedAbsorption κ q N A c :=
  normalizedAbsorption_of_activeFinal κ (activeFinal_holds κ)

theorem theorem22_strict (κ : LocalKernelClass) :
    ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∃ Cst : ℝ, ∀ N, finiteDepthConstant κ q N ≤ Cst := by
  obtain ⟨q, hq2, hq3, h⟩ := proposition23 κ
  let K : ℝ := 4 / 3 * 16 ^ (4 / q)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨A, hA, hN⟩ := h (1 / 2 / K) (by positivity)
  have hsmall : K * (1 / 2 / K) ≤ 1 / 2 := by
    exact le_of_eq (mul_div_cancel₀ _ hK.ne')
  exact ⟨q, hq2, hq3, 2 + 2 * K * A,
    uniform_local_of_normalized κ hq2.le hA (by positivity) hsmall hN⟩

end OpenAI086.ReferenceV60
#print axioms OpenAI086.ReferenceV60.proposition23
#print axioms OpenAI086.ReferenceV60.theorem22_strict
#print axioms Auto.retainedMin_holds
#print axioms Auto.activeFinal_holds
#print axioms Auto.normalizedAbsorption_of_activeFinal
#print axioms Auto.tht_main
#print axioms Auto.activeCellReduction
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.attempt_localization
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.side_estimate_leaf
