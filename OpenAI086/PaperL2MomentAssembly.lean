import Mathlib
import OpenAI086.PaperStoppingPartition

/-! Lemma 3.4: Hilbert-space local refits and actual L² assembly. The
cut-support orthogonality is explicit; the dyadic L∞ and maximal estimates
remain separate. -/
namespace OpenAI086
open MeasureTheory

/-- Glue orthogonal residuals to preserve a global moment. The local test
vectors are restrictions of the old column to the cut atoms. -/
theorem v22_glue_cut_moments {Q X : Type*} [Fintype Q]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (g z φ : Q → X)
    (hlocal : ∀ q, inner ℂ (g q) (φ q) = inner ℂ (z q) (φ q))
    (hoff : ∀ q r, q ≠ r → inner ℂ (g q) (φ r) = 0 ∧ inner ℂ (z q) (φ r) = 0) :
    inner ℂ (∑ q, g q) (∑ q, φ q) = inner ℂ (∑ q, z q) (∑ q, φ q) := by
  classical
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases he : q = r
  · subst r; exact hlocal q
  · rw [(hoff q r he).1, (hoff q r he).2]

/-- The moment identity on the actual Bochner L² space, not a coordinate
sample. Cut atoms are supplied as L² pieces; proving locality of their
concrete restrictions and existence of the refits is still required. -/
theorem v22_L2_cut_moment {Ω Q H : Type*} [MeasurableSpace Ω] [Fintype Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure Ω) (g z φ : Q → Lp H 2 μ)
    (hlocal : ∀ q, inner ℂ (g q) (φ q) = inner ℂ (z q) (φ q))
    (hoff : ∀ q r, q ≠ r → inner ℂ (g q) (φ r) = 0 ∧ inner ℂ (z q) (φ r) = 0) :
    inner ℂ (∑ q, g q) (∑ q, φ q) = inner ℂ (∑ q, z q) (∑ q, φ q) :=
  v22_glue_cut_moments g z φ hlocal hoff

/-- Given a refit in a subspace whose residual is orthogonal to that
subspace, its coefficient-free energy identity follows. -/
theorem v22_refit_energy_complex {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (V : Submodule ℂ X) (z g : X)
    (hg : g ∈ V) (horth : ∀ φ ∈ V, inner ℂ (z-g) φ = 0) :
    inner ℂ z g = inner ℂ g g := by
  have h := horth g hg
  rw [inner_sub_left, sub_eq_zero] at h
  exact h

/-- Patch energy identity and orthogonality across all cut atoms. -/
theorem v22_glue_cut_energy {Q X : Type*} [Fintype Q]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (g z : Q → X)
    (hlocal : ∀ q, inner ℂ (g q) (g q) = inner ℂ (z q) (g q))
    (hoff : ∀ q r, q ≠ r → inner ℂ (g q) (g r) = 0 ∧ inner ℂ (z q) (g r) = 0) :
    inner ℂ (∑ q, g q) (∑ q, g q) = inner ℂ (∑ q, z q) (∑ q, g q) :=
  v22_glue_cut_moments g z g hlocal hoff

/-- Construct a cut-cell refit with Mathlib's actual orthogonal projection
onto the local subspace. No residual-orthogonality premise is needed. -/
theorem v22_construct_refit {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (V : Submodule ℂ X) [V.HasOrthogonalProjection] (z : X) :
    ∃ g ∈ V, ∀ φ ∈ V, inner ℂ g φ = inner ℂ z φ := by
  refine ⟨V.starProjection z, V.starProjection_apply_mem z, ?_⟩
  intro φ hφ
  have h := Submodule.starProjection_inner_eq_zero (K := V) z φ hφ
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

/-- Actual L² local refits assembled by finite sums. The local subspaces
must admit orthogonal projections and the cut pieces have disjoint-support
orthogonality. Identifying these conditions for the concrete dyadic cuts
and proving pointwise bounds are the remaining compression steps. -/
theorem v22_construct_L2_refits {Ω Q H : Type*} [MeasurableSpace Ω] [Fintype Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure Ω) (V : Q → Submodule ℂ (Lp H 2 μ))
    [∀ q, (V q).HasOrthogonalProjection] (z φ : Q → Lp H 2 μ)
    (hφ : ∀ q, φ q ∈ V q)
    (hoff : ∀ q r, q ≠ r → ∀ g ∈ V q, inner ℂ g (φ r) = 0)
    (hzoff : ∀ q r, q ≠ r → inner ℂ (z q) (φ r) = 0) :
    ∃ g : Q → Lp H 2 μ, (∀ q, g q ∈ V q) ∧
      inner ℂ (∑ q, g q) (∑ q, φ q) = inner ℂ (∑ q, z q) (∑ q, φ q) := by
  choose g hg hm using fun q => v22_construct_refit (V q) (z q)
  refine ⟨g, hg, v22_L2_cut_moment μ g z φ (fun q => hm q (φ q) (hφ q)) ?_⟩
  intro q r hne
  exact ⟨hoff q r hne (g q) (hg q), hzoff q r hne⟩

end OpenAI086
