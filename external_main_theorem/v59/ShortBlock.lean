import TrilinearHT.Auto.Sec14_2bShortBlockSummation

/-! Lemma 7.2 on the reference's concrete tree and kernel data. The
reference's improved exponent 2(q-2)/(q-1) implies the printed
C(q-2) exponent. Its proof uses an alternative heavy-slot estimate.
No assumption of a pre-proved short-block estimate is introduced. -/
namespace OpenAI086.ReferenceV59
open Auto MeasureTheory
open scoped ENNReal BigOperators

theorem lemma72 (κ : LocalKernelClass) {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3)
    {C4 : ℝ} (hC4 : 0 ≤ C4) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (G : RealDyadicGrid) (K Nd : ℕ) (d₀ : ℤ),
      ∀ (T : ShortBlockTree G K) {E : Type*} [NormedAddCommGroup E] (z : Fin 4 → ℝ → E),
      (∀ j, Measurable fun y => ‖z j y‖) → ∀ s : Fin 4 → ℝ, (∀ j, 0 ≤ s j) →
      (∀ j, ∀ L ∈ T.leaves, ∫⁻ y in dyadicGridCell G L.1 L.2, ‖z j y‖ₑ ^ 2 ≤
        ENNReal.ofReal (s j ^ 2 * dyadicGridLength G L.1)) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (zσ : Fin 4 → Ω → ℝ → ℂ), (∀ j, Measurable (Function.uncurry (zσ j))) →
      (∀ j y, (∫⁻ σ, ‖zσ j σ y‖ₑ ^ (4 : ℝ) ∂P) ^ (1 / 4 : ℝ) ≤ ENNReal.ofReal C4 * ‖z j y‖ₑ) →
      ∀ (kernel : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ T.internal, IsAdmissibleLocalKernel κ
        (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (kernel I)) →
      ∀ cells ⊆ T.internal, (∀ I ∈ cells, d₀ ≤ I.1 ∧ I.1 < d₀ + Nd) →
      ∀ ε : ℤ × ℤ → Ω → ℂ, (∀ I, Measurable (ε I)) → (∀ I σ, ‖ε I σ‖ ≤ 1) →
      ∫⁻ σ, ‖∑ I ∈ cells, (dyadicGridLength G I.1 : ℂ) * ε I σ *
        localProgressionForm (dyadicGridLength G I.1) (kernel I) (fun j => zσ j σ)‖ₑ ∂P ≤
        ENNReal.ofReal (Cq * (1 + finiteDepthConstant κ q Nd) *
          (1 + Real.log ((K : ℝ) + 2)) * ((K : ℝ) + 2) ^ (2 * (q - 2)) *
          dyadicGridLength G T.root.1 * ∏ j, s j) := by
  obtain ⟨Cq, hCq, h⟩ := Auto.short_block_comparison κ hq2 hq3 hC4
  refine ⟨Cq, hCq, ?_⟩
  intro G K Nd d₀ T E _ z hz s hs hleaf Ω _ P _ zσ hzσ hmom kernel hker cells hcells hwin ε hε hε1
  have hb := h G K Nd d₀ T z hz s hs hleaf P zσ hzσ hmom kernel hker cells hcells hwin ε hε hε1
  have he : 2 * (q - 2) / (q - 1) ≤ 2 * (q - 2) := by
    apply (div_le_iff₀ (by linarith : 0 < q - 1)).mpr
    nlinarith [sq_nonneg (q - 2)]
  have hp : ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) ≤
      ((K : ℝ) + 2) ^ (2 * (q - 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K]) he
  have hCN : 0 ≤ finiteDepthConstant κ q Nd :=
    le_trans zero_le_one (finiteDepthConstant_bounds κ (by linarith) Nd).1
  have hl : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) K])
  have hr := (dyadicGridLength_pos G T.root.1).le
  have hsprod : 0 ≤ ∏ j, s j := Finset.prod_nonneg (fun j _ => hs j)
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

end OpenAI086.ReferenceV59
#print axioms OpenAI086.ReferenceV59.lemma72
