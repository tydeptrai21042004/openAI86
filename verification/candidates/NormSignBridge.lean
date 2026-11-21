import Mathlib

/-!
# Candidate: the L¹ norm is invariant under a global sign

This file is NOT part of the trusted root. It must typecheck in the pinned
Mathlib toolchain before it can be imported into `OpenAI086`.
-/

noncomputable section
namespace OpenAI086
open MeasureTheory

/-- Invariance of the `eLpNorm` under pointwise complex negation. -/
theorem eLpNorm_complex_neg_candidate (g : ℝ → ℂ) :
    eLpNorm (fun x : ℝ => -g x) 1 = eLpNorm g 1 := by
  have h : (fun x : ℝ => -g x) = -g := rfl
  rw [h]
  exact eLpNorm_neg g 1

#print axioms OpenAI086.eLpNorm_complex_neg_candidate
end OpenAI086
