import OpenAI086.PaperV44L2Projection

/-! Compression bridge: finite measurable cuts and genuine L² spaces.
An inherited coarse column splits into its restrictions on the finer cut.
No cross-layer commutation is asserted. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

variable {Ω H Q : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [Fintype Q]

/-- The indicator decomposition of a column over a finite measurable
partition, proved pointwise from the unique containing atom. -/
theorem v44_cut_indicator_sum (A : Q → Set Ω) (S : Set Ω) (f : Ω → H)
    (hpartition : ∀ x ∈ S, ∃! q, x ∈ A q)
    (hsub : ∀ q, A q ⊆ S) (x : Ω) :
    (∑ q, (A q).indicator f x) = S.indicator f x := by
  classical
  by_cases hx : x ∈ S
  · obtain ⟨q, hq, hu⟩ := hpartition x hx
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single q]
    · rw [Set.indicator_of_mem hq]
    · intro r _ hr
      apply Set.indicator_of_notMem
      intro h
      exact hr (hu r h)
    · simp
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro q _
    exact Set.indicator_of_notMem (fun h => hx (hsub q h)) _

/-- Refinement inclusion in the actual L² space follows from a coarse
column's partition identity and inheritance of the corresponding finer
columns. The refinement may have arbitrary finite size. -/
theorem v44_l2_span_refinement {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : Measure Ω) (φ : ι → Ω → H) (ψ : κ → Ω → H)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ j, MemLp (ψ j) 2 μ)
    (h : ∀ i, ∃ c : κ → ℂ, ∀ᵐ x ∂μ, (∑ j, c j • ψ j x) = φ i x) :
    v44ColumnSpan (v44L2Columns μ φ hφ) ≤ v44ColumnSpan (v44L2Columns μ ψ hψ) := by
  apply v44_span_refinement
  intro i
  obtain ⟨c, hc⟩ := h i
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [v44_l2_sum_ae μ ψ hψ c, MemLp.coeFn_toLp (hφ i), hc] with x h1 h2 h3
  change (∑ j, c j • v44L2Columns μ ψ hψ j) x = ((hφ i).toLp (φ i)) x
  rw [h1, h2, h3]

/-- Actual nested projections on the common ambient L², with the
algebraic relation required by the nested-prefix lemma. -/
theorem v44_nested_refit {X ι κ : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [Fintype ι] [Fintype κ]
    (Φ : ι → X) (Ψ : κ → X) (h : v44ColumnSpan Φ ≤ v44ColumnSpan Ψ) (z : X) :
    v44Projection Φ (v44Projection Ψ z) = v44Projection Φ z := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((v44ColumnSpan Φ).starProjection_apply_mem z)
  intro w hw
  rw [inner_sub_left, v44_projection_moment Ψ z w (h hw),
    v44_projection_moment Φ z w hw, sub_self]

end OpenAI086
