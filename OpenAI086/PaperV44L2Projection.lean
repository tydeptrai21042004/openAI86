import Mathlib

/-! Continuous Hilbert-space construction for the finite-column refits in
Sections 3.2–3.4. In particular the ambient space may be an actual Bochner L²
space, not a discretization. Finite-dimensionality applies only to the selected
column span, never to the ambient space or to the number of spatial branches.
Source proof candidates; kernel checking is required. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

section Span
variable {X ι : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [Fintype ι]

def v44ColumnSpan (Φ : ι → X) : Submodule ℂ X := Submodule.span ℂ (Set.range Φ)

instance v44SpanFinite (Φ : ι → X) : Module.Finite ℂ (v44ColumnSpan Φ) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range Φ)

instance v44SpanProjection (Φ : ι → X) : (v44ColumnSpan Φ).HasOrthogonalProjection := by
  infer_instance

/-- The projection is constructed, not supplied as a hypothesis. -/
def v44Projection (Φ : ι → X) : X →L[ℂ] X := (v44ColumnSpan Φ).starProjection

theorem v44_projection_repr (Φ : ι → X) (z : X) :
    ∃ c : ι → ℂ, (∑ i, c i • Φ i) = v44Projection Φ z := by
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
  exact (v44ColumnSpan Φ).starProjection_apply_mem z

/-- Orthogonality with the actual projection on the left, using Mathlib's
conjugate-linear-first convention. -/
theorem v44_projection_moment (Φ : ι → X) (z w : X) (hw : w ∈ v44ColumnSpan Φ) :
    inner ℂ (v44Projection Φ z) w = inner ℂ z w := by
  have h := Submodule.starProjection_inner_eq_zero (K := v44ColumnSpan Φ) z w hw
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem v44_projection_energy (Φ : ι → X) (z : X) :
    inner ℂ (v44Projection Φ z) (v44Projection Φ z) =
      inner ℂ z (v44Projection Φ z) :=
  v44_projection_moment Φ z _ ((v44ColumnSpan Φ).starProjection_apply_mem z)

/-- If the private coordinates give injective synthesis, the actual
orthogonal projection has unique constant coefficients. -/
theorem v44_projection_unique_coeff (Φ : ι → X) (z : X)
    (hinj : Function.Injective (fun c : ι → ℂ => ∑ i, c i • Φ i)) :
    ∃! c : ι → ℂ, (∑ i, c i • Φ i) = v44Projection Φ z := by
  obtain ⟨c, hc⟩ := v44_projection_repr Φ z
  exact ⟨c, hc, fun d hd => hinj (hd.trans hc.symm)⟩

/-- A column family that refits on a finer partition yields nested spans
once each coarse column is expressed as a sum of finer columns. -/
theorem v44_span_refinement {κ : Type*} [Fintype κ]
    (Φ : ι → X) (Ψ : κ → X)
    (h : ∀ i, ∃ c : κ → ℂ, (∑ j, c j • Ψ j) = Φ i) :
    v44ColumnSpan Φ ≤ v44ColumnSpan Ψ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr (h i)

end Span

section L2
variable {Ω H ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [Fintype ι]

/-- Lift each actual measurable column into the Bochner L² space. -/
def v44L2Columns (μ : Measure Ω) (φ : ι → Ω → H)
    (hφ : ∀ i, MemLp (φ i) 2 μ) : ι → Lp H 2 μ :=
  fun i => (hφ i).toLp (φ i)

/-- Evaluation of a finite linear combination in L² agrees almost everywhere
with the finite pointwise combination of representatives. -/
theorem v44_l2_sum_ae (μ : Measure Ω) (φ : ι → Ω → H)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (c : ι → ℂ) :
    (fun x => (∑ i, c i • v44L2Columns μ φ hφ i) x) =ᵐ[μ]
      fun x => ∑ i, c i • φ i x := by
  classical
  have hs (s : Finset ι) :
      (fun x => (∑ i ∈ s, c i • v44L2Columns μ φ hφ i) x) =ᵐ[μ]
        fun x => ∑ i ∈ s, c i • φ i x := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact Lp.coeFn_zero
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        filter_upwards [Lp.coeFn_add (c i • v44L2Columns μ φ hφ i)
          (∑ j ∈ s, c j • v44L2Columns μ φ hφ j),
          Lp.coeFn_smul (c i) (v44L2Columns μ φ hφ i),
          MemLp.coeFn_toLp (hφ i), ih] with x h1 h2 h3 h4
        change ((c i • v44L2Columns μ φ hφ i) +
          ∑ j ∈ s, c j • v44L2Columns μ φ hφ j) x = _
        rw [h1]
        change (c i • v44L2Columns μ φ hφ i) x +
          (∑ j ∈ s, c j • v44L2Columns μ φ hφ j) x = _
        rw [h2, h4]
        change c i • ((hφ i).toLp (φ i)) x + _ = _
        rw [h3]
  exact hs Finset.univ

/-- Continuous L² refit with constant coefficients, and all its integrated
normal equations. No assumed projection or normal equations. -/
theorem v44_L2_refit (μ : Measure Ω) (φ : ι → Ω → H)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (z : Lp H 2 μ) :
    ∃ c : ι → ℂ,
      (fun x => v44Projection (v44L2Columns μ φ hφ) z x) =ᵐ[μ]
        (fun x => ∑ i, c i • φ i x) ∧
      (∀ i, (∫ x, inner ℂ (φ i x) (z x) ∂μ) =
        ∫ x, inner ℂ (φ i x) (∑ j, c j • φ j x) ∂μ) := by
  let Φ := v44L2Columns μ φ hφ
  obtain ⟨c, hc⟩ := v44_projection_repr Φ z
  have hre : (fun x => v44Projection Φ z x) =ᵐ[μ]
      (fun x => ∑ i, c i • φ i x) := by
    rw [← hc]
    exact v44_l2_sum_ae μ φ hφ c
  refine ⟨c, hre, ?_⟩
  intro i
  have hm := v44_projection_moment Φ z (Φ i)
    (Submodule.subset_span (Set.mem_range_self i))
  have hm' : inner ℂ (Φ i) z = inner ℂ (Φ i) (v44Projection Φ z) := by
    have h := congrArg (starRingEnd ℂ) hm.symm
    simpa only [inner_conj_symm] using h
  simp only [MeasureTheory.L2.inner_def] at hm'
  calc
    _ = ∫ x, inner ℂ (Φ i x) (z x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (hφ i)] with x hx
      change inner ℂ (φ i x) (z x) = inner ℂ (((hφ i).toLp (φ i)) x) (z x)
      rw [hx]
    _ = _ := hm'.trans (integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp (hφ i), hre] with x hx hy
      change inner ℂ (((hφ i).toLp (φ i)) x) (v44Projection Φ z x) = _
      rw [hx, hy]))

/-- The paper's normalized local measure can be passed as μ; the integrated
energy equality holds on any measure space, even without normalization. -/
theorem v44_L2_energy (μ : Measure Ω) (φ : ι → Ω → H)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (z : Lp H 2 μ) :
    (∫ x, inner ℂ (v44Projection (v44L2Columns μ φ hφ) z x)
      (v44Projection (v44L2Columns μ φ hφ) z x) ∂μ) =
    ∫ x, inner ℂ (z x) (v44Projection (v44L2Columns μ φ hφ) z x) ∂μ := by
  simpa only [MeasureTheory.L2.inner_def] using
    v44_projection_energy (v44L2Columns μ φ hφ) z

end L2
end OpenAI086
