import Mathlib
import OpenAI086.PaperStatement
import OpenAI086.PrincipalValueGoals

/-!
# Candidate: pointwise principal-value transfer under a proven sign identity

The theorem below is an unconditional topological fact. Applied after
`truncationSignBridge`, it changes the plus-shift limit to the exact
minus-shift limit of the PDF. It is NOT a proof of the plus-shift bound
or the existence of that limit.

STATUS: candidate; no local Lean kernel run.
-/

noncomputable section
namespace OpenAI086
open Filter Topology

/-- A pointwise global sign identity transfers a limit at `ε → 0+`.
The continuity of complex negation is used by Mathlib's `.neg`. -/
theorem tendsto_under_global_sign
    (minus plus : ℝ → ℂ) (z : ℂ)
    (hsign : ∀ ε, minus ε = -plus ε)
    (hplus : Tendsto plus (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    Tendsto minus (𝓝[>] (0 : ℝ)) (𝓝 (-z)) := by
  have hfun : minus = fun ε => -plus ε := funext hsign
  rw [hfun]
  exact hplus.neg

/-- Conditional transfer to the PDF's pointwise principal-value target.
The only remaining hypotheses are the actual, explicitly stated analytic
ones: plus-shift convergence and exact finite-truncation sign. -/
theorem minus_principal_value_from_plus
    (f : Fin 3 → SchwartzMap ℝ ℂ)
    (hsgn : ∀ x ε, truncHilbert (fun i => f i) x ε =
      -(plusTruncHilbert (fun i => f i) x ε))
    (Tf : ℝ → ℂ)
    (hplus : ∀ x, Tendsto
      (fun ε => plusTruncHilbert (fun i => f i) x ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (Tf x))) :
    ∀ x, Tendsto
      (fun ε => truncHilbert (fun i => f i) x ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Tf x)) := by
  intro x
  apply tendsto_under_global_sign
    (fun ε => truncHilbert (fun i => f i) x ε)
    (fun ε => plusTruncHilbert (fun i => f i) x ε)
    (Tf x) (hsgn x) (hplus x)

#print axioms OpenAI086.minus_principal_value_from_plus
end OpenAI086
