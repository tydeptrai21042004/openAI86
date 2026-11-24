import Mathlib
import OpenAI086.PaperL2MomentAssembly

/-! Concrete measurable cut restrictions. These are Bochner L² elements,
not a sampled grid. Local spans and the maximal-function bound remain open. -/
namespace OpenAI086
open MeasureTheory

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

noncomputable def v23RestrictL2 (μ : Measure Ω) (s : Set Ω)
    (hs : MeasurableSet s) (f : Lp H 2 μ) : Lp H 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator (fun x => f x))

theorem v23_restrict_ae (μ : Measure Ω) (s : Set Ω)
    (hs : MeasurableSet s) (f : Lp H 2 μ) :
    (fun x => v23RestrictL2 μ s hs f x) =ᵐ[μ] s.indicator (fun x => f x) := by
  unfold v23RestrictL2
  exact MemLp.coeFn_toLp _

/-- Orthogonality follows from actual disjoint support, not an assumed
inner product identity. -/
theorem v23_L2_disjoint_support (μ : Measure Ω) (s t : Set Ω)
    (f g : Lp H 2 μ) (hst : Disjoint s t)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0)
    (hg : ∀ᵐ x ∂μ, x ∉ t → g x = 0) : inner ℂ f g = 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    _ = ∫ _x : Ω, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hfx hgx
      by_cases hx : x ∈ s
      · have ht : x ∉ t := fun ht => Set.disjoint_left.mp hst hx ht
        rw [hgx ht, inner_zero_right]
      · rw [hfx hx, inner_zero_left]
    _ = 0 := by simp

theorem v23_restrict_orthogonal (μ : Measure Ω) (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t)
    (f g : Lp H 2 μ) :
    inner ℂ (v23RestrictL2 μ s hs f) (v23RestrictL2 μ t ht g) = 0 := by
  apply v23_L2_disjoint_support μ s t _ _ hst
  · filter_upwards [v23_restrict_ae μ s hs f] with x hx
    intro h; rw [hx, Set.indicator_of_notMem h]
  · filter_upwards [v23_restrict_ae μ t ht g] with x hx
    intro h; rw [hx, Set.indicator_of_notMem h]

end OpenAI086
