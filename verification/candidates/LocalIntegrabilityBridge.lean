import Mathlib
import OpenAI086.GlobalLipschitzCancellation

/-!
# Candidate for local Bochner integrability of the paired kernel

This is deliberately not part of the trusted import tree.  The exact
Mathlib declaration must be elaborated using the project's pinned
Lean/Mathlib toolchain before it can be promoted.

The analytic logic is: a.e. strongly measurable + uniformly bounded on a
set of finite Lebesgue measure implies integrability on that set.
-/

namespace OpenAI086
noncomputable section
open MeasureTheory

/-- Local integrability is the next logical step after the pointwise
uniform bound. Measurability remains an explicit hypothesis. -/
theorem paired_kernel_integrable_on_unit_candidate
    (f : Fin 3 → ℝ → ℂ) (x B : ℝ)
    (hMeas : AEStronglyMeasurable (pairedHilbertKernel f x)
        (volume : Measure ℝ))
    (hBound : ∀ t : ℝ, ‖pairedHilbertKernel f x t‖ ≤ B) :
    IntegrableOn (pairedHilbertKernel f x) (Set.Icc (0 : ℝ) 1)
        (volume : Measure ℝ) := by
  have hfinite : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    simp
  apply Measure.integrableOn_of_bounded hfinite hMeas
  exact Filter.Eventually.of_forall hBound

end
end OpenAI086
