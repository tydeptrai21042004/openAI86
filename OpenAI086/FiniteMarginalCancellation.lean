import Mathlib

/-!
# OpenAI #086, Lemma 2.4: finite-difference marginal cancellation model

The continuous paper constructs W as a product of directional derivatives.
For finitely supported discrete differences along a progression line,
endpoint cancellation is an exact telescoping identity.  This file proves
that discrete analogue, not the continuous Gevrey derivative/integral case.
-/

namespace OpenAI086

/-- The sum of consecutive differences on a finite discrete interval. -/
def discreteMarginal (g : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, (g (k + 1) - g k)

/-- Discrete fundamental theorem of calculus (no smoothness needed). -/
theorem discreteMarginal_eq_endpoints (g : ℕ → ℂ) (N : ℕ) :
    discreteMarginal g N = g N - g 0 := by
  induction N with
  | zero => simp [discreteMarginal]
  | succ n ih =>
      simp only [discreteMarginal, Finset.sum_range_succ] at ih ⊢
      rw [ih]
      abel

/-- If both endpoints vanish, the entire discrete marginal vanishes. -/
theorem discreteMarginal_zero (g : ℕ → ℂ) (N : ℕ)
    (h₀ : g 0 = 0) (hN : g N = 0) :
    discreteMarginal g N = 0 := by
  rw [discreteMarginal_eq_endpoints, h₀, hN, sub_self]

/-- One-point progression marginal for any of the four paper slots.
All arithmetic is kept in the actual progression coordinates. -/
def discreteProgressionMarginal
    (F : ℝ → ℝ → ℂ) (j : Fin 4) (u : ℝ) (N : ℕ) : ℂ :=
  discreteMarginal
    (fun n => F (u - (j.val : ℝ) * (n : ℝ)) (n : ℝ)) N

/-- Discrete marginal cancellation along a line of constant `x+j*t`. -/
theorem discreteProgressionMarginal_zero
    (F : ℝ → ℝ → ℂ) (j : Fin 4) (u : ℝ) (N : ℕ)
    (hstart : F u 0 = 0)
    (hend : F (u - (j.val : ℝ) * (N : ℝ)) (N : ℝ) = 0) :
    discreteProgressionMarginal F j u N = 0 := by
  unfold discreteProgressionMarginal
  apply discreteMarginal_zero
  · simpa using hstart
  · exact hend

end OpenAI086
