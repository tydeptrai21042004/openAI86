import Mathlib

/-!
# OpenAI #086, §2: scalar absorption and telescoping reductions.

No analytic inequality is assumed or declared proved in this file.
-/

namespace OpenAI086

/-- Algebraic absorption, after the analytic estimate `C ≤ A + θ C` is known. -/
theorem absorb_estimate (A C θ : ℝ) (hθ : θ < 1)
    (h : C ≤ A + θ * C) : C ≤ A / (1 - θ) := by
  have hpos : 0 < 1 - θ := by linarith
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- Finite telescoping for successive differences. -/
theorem finite_telescoping (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (u (n + 1) - u n)) = u N - u 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Uniform geometric decay from a scalar one-step contraction. -/
theorem decay_of_contraction (mass : ℕ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hstep : ∀ n, mass (n + 1) ≤ ρ * mass n) :
    ∀ n, mass n ≤ ρ ^ n * mass 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        mass (n + 1) ≤ ρ * mass n := hstep n
        _ ≤ ρ * (ρ ^ n * mass 0) := mul_le_mul_of_nonneg_left ih hρ
        _ = ρ ^ (n + 1) * mass 0 := by rw [pow_succ]; ring

end OpenAI086
