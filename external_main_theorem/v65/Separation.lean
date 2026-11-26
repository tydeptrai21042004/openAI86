import TrilinearHT.Auto.Sec09_2ChartFourierSeparation

/-! Lemmas 4.5 and 4.6: adapt the pinned reference (Roos/Claude, Apache-2.0)
to all chart dimensions and bounded-atom separated kernels. -/
namespace OpenAI086.ReferenceV65
open Auto MeasureTheory
open scoped ComplexConjugate FourierTransform BigOperators ENNReal

/-- Lemma 4.5, including the dimension-zero cases allowed by Definition 4.1.
Pad both charts by a unit atom before applying the reference separation.
The explicit budget uses the padded complexity, not the original H. -/
theorem progression_all_dimensions (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ c₁ D : ℕ, 1 ≤ c₁ ∧ 1 ≤ D ∧ ∃ W₀ : ℝ, Real.exp 2 ≤ W₀ ∧
    ∀ {d e : ℕ} (H : ℝ) (A : QuadraticChartData d) (A' : QuadraticChartData e),
      QuadraticChartComplexity c₀ H A → QuadraticChartComplexity c₀ H A' →
      ∀ i k a b : ℤ, a ≠ b → |i| ≤ 3 → |k| ≤ 3 → |a| ≤ 3 → |b| ≤ 3 →
      let X := 1 + Real.log (max H W₀ ^ 6)
      ∃ (τ : Type) (_ : Countable τ) (cf : τ → ℂ) (φa φb φt : τ → QuadraticChartData ((d + 1) + (e + 1)))
        (size : τ → ℝ),
        (∀ x t : ℝ, HasSum (fun q => cf q * quadraticChartAtom (φa q) (x + a * t) *
            quadraticChartAtom (φb q) (x + b * t) * quadraticChartAtom (φt q) t)
          (quadraticChartAtom A (x + i * t) * quadraticChartAtom A' (x + k * t))) ∧
        (∀ q, IsBoundedQuadraticChart (φa q) ∧ IsBoundedQuadraticChart (φb q) ∧
          IsBoundedQuadraticChart (φt q)) ∧
        (∀ q, 1 ≤ size q) ∧
        Summable (fun q => ‖cf q‖) ∧ (∑' q, ‖cf q‖) ≤ Real.exp (D * X ^ D) ∧
        (∀ T : ℝ, 1 ≤ T → (∑' q, if T ≤ size q then ‖cf q‖ else 0) ≤
          Real.exp (D * X ^ D) / T ^ 100) ∧
        (∀ q, QuadraticChartComplexity c₁ ((Real.exp (D * X ^ D) * size q) ^ 6) (φa q) ∧
          QuadraticChartComplexity c₁ ((Real.exp (D * X ^ D) * size q) ^ 6) (φb q) ∧
          QuadraticChartComplexity c₁ ((Real.exp (D * X ^ D) * size q) ^ 6) (φt q)) ∧
        (∀ T : ℝ, 1 ≤ T → ∃ Qs : Finset τ, (∀ q, size q ≤ T → q ∈ Qs) ∧
          (Qs.card : ℝ) ≤ Real.exp (10 * X ^ 2) * (3 * T) ^ (3 * ((d + 1) + (e + 1)))) := by
  obtain ⟨cp, W₀, hcp, hW₀, hpad⟩ := exists_pad_chart
  obtain ⟨c₁, D, hc₁, hD, hsep⟩ := progressionSeparation (max c₀ cp)
    (le_trans hc (le_max_left _ _))
  refine ⟨c₁, D, hc₁, hD, W₀, hW₀, ?_⟩
  intro d e H A A' hA hA' i k a b hab hi hk ha hb
  obtain ⟨P, hP, hPc, _⟩ := hpad A hA hc
  obtain ⟨Q, hQ, hQc, _⟩ := hpad A' hA' hc
  obtain ⟨τ, hτ, cf, φa, φb, φt, size, hsum, hbound, hsize, hmass, hmassBound,
    htail, hcomplex, hcount, _⟩ := hsep (max H W₀ ^ 6) P Q (by omega) (by omega)
      hPc hQc i k a b hab hi hk ha hb
  refine ⟨τ, hτ, cf, φa, φb, φt, size, ?_, hbound, hsize, hmass, hmassBound,
    htail, hcomplex, hcount⟩
  intro x t
  simpa only [hP, hQ] using hsum x t

/-- Lemma 4.6: retain the reference uniform approximation and realize each
separated linear character as a bounded chart of fixed complexity. -/
theorem separated_kernel_atoms (c₀ : ℕ) (hc : 1 ≤ c₀) (R : ℝ) (hR : 1 ≤ R)
    (κ : LocalKernelClass) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ {d : ℕ} (H δ ε r a₀ : ℝ) (A : QuadraticChartData d),
      QuadraticChartComplexity c₀ H A → 0 < r →
      ∀ w : ℝ × ℝ → ℂ, IsAdmissibleLocalKernel κ a₀ r w →
      ∀ ζ : ℝ → ℂ, Measurable ζ → (∀ u, ‖ζ u‖ ≤ H) → (∀ u v, ‖ζ v - ζ u‖ ≤ H * |v - u|) →
      (∀ u, ζ u ≠ 0 → |u| ≤ R) → 0 < δ → 0 < ε → ε ≤ 1 →
      (∀ s < δ, ∃ ξ : ℝ, s < ‖∫ u, (Real.fourierChar (-(u * ξ)) : ℂ) *
        (ζ u * quadraticChartAtom A (r * u))‖) →
      ∀ sa sb : ℝ, 1 ≤ |sb - sa| → |sa| ≤ 3 →
      let X := 1 + Real.log H + Real.log (max 1 δ⁻¹) + Real.log ε⁻¹
      ∃ (ι' : Type) (_ : Fintype ι') (c : ι' → ℂ) (φa φb : ι' → QuadraticChartData 0),
        (Fintype.card ι' : ℝ) ≤ Real.exp (D * X ^ D) ∧
        (∑ ν, ‖c ν‖) ≤ Real.exp (D * X ^ D) ∧
        (∀ ν, QuadraticChartComplexity c₀ (Real.exp 2) (φa ν) ∧
          QuadraticChartComplexity c₀ (Real.exp 2) (φb ν) ∧
          IsBoundedQuadraticChart (φa ν) ∧ IsBoundedQuadraticChart (φb ν)) ∧
        ∀ ya yb : ℝ, ya ∈ Set.Icc a₀ (a₀ + r) → yb ∈ Set.Icc a₀ (a₀ + r) →
          ‖w (ya - sa * ((yb - ya) / (sb - sa)), (yb - ya) / (sb - sa)) *
              quadraticChartAtom A ((yb - ya) / (sb - sa)) -
            ∑ ν, c ν * quadraticChartAtom (φa ν) ya *
              quadraticChartAtom (φb ν) yb‖ ≤ ε  := by
  obtain ⟨D, hD, happrox⟩ := separatedKernelApprox c₀ hc R hR κ
  refine ⟨D, hD, ?_⟩
  intro d H δ ε r a₀ A hA hr w hw ζ hζm hζb hζL hζs hδ hε hε1 hcorr sa sb hsep hsa
  obtain ⟨ι, hι, c, α, β, hcard, hmass, happ⟩ :=
    happrox H δ ε r a₀ A hA hr w hw ζ hζm hζb hζL hζs hδ hε hε1 hcorr sa sb hsep hsa
  refine ⟨ι, hι, c, (fun ν => ordinaryQuadraticChart 0 (α ν)),
    (fun ν => ordinaryQuadraticChart 0 (β ν)), hcard, hmass, ?_, ?_⟩
  · intro ν
    exact ⟨ordinaryQuadraticChart_complexity c₀ le_rfl 0 (α ν),
      ordinaryQuadraticChart_complexity c₀ le_rfl 0 (β ν),
      ordinaryQuadraticChart_bounded 0 (α ν), ordinaryQuadraticChart_bounded 0 (β ν)⟩
  · intro ya yb hya hyb
    simpa only [ordinaryQuadraticChart_atom, zero_mul, zero_add] using happ ya yb hya hyb

end OpenAI086.ReferenceV65
#print axioms OpenAI086.ReferenceV65.progression_all_dimensions
#print axioms OpenAI086.ReferenceV65.separated_kernel_atoms
