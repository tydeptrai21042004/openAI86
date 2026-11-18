import Mathlib
import OpenAI086.Packing

/-!
# Uniform abstract absorption (OpenAI #086, Section 2)

This is the precise SCALAR inference from a family of estimates
`C_N ≤ A + θ*C_N` to a bound independent of `N`.  The ANALYTIC step of
establishing this inequality for the local-form constants is not provided.
-/

namespace OpenAI086

/-- A uniform-in-N absorption principle. -/
theorem uniform_absorption (C : ℕ → ℝ) (A θ : ℝ)
    (hθ : θ < 1) (h : ∀ N, C N ≤ A + θ * C N) :
    ∀ N, C N ≤ A / (1 - θ) := by
  intro N
  exact absorb_estimate A (C N) θ hθ (h N)

/-- Finite sums with a geometrically shrinking generation budget
inherit the same constant, independently of the truncation depth. -/
theorem uniform_packing_control (mass : ℕ → ℝ) (A ρ : ℝ)
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hroot : 0 ≤ mass 0)
    (hstep : ∀ n, mass (n+1) ≤ ρ * mass n) (N : ℕ) :
    (∑ n ∈ Finset.range N, A * mass n) ≤ A * mass 0 / (1 - ρ) := by
  calc
    (∑ n ∈ Finset.range N, A * mass n)
        = A * (∑ n ∈ Finset.range N, mass n) := by
            rw [Finset.mul_sum]
    _ ≤ A * (mass 0 / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left
            (packing_of_contracted_generations mass ρ hρ0 hρ1 hroot hstep N) hA
    _ = A * mass 0 / (1 - ρ) := by ring

end OpenAI086
