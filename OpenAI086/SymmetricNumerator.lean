import Mathlib

/-!
# Independent local cancellation for the trilinear Hilbert transform

The symmetrized principal value pairs `t` and `-t`. Its numerator is a
THREE-FACTOR DIFFERENCE, and the exact telescoping decomposition below
reduces its control to three first differences of Schwartz inputs.

This establishes the algebraic and norm-inequality steps only; the
Schwartz derivative estimates and Bochner integrability are separate.
This file is independently authored and imports Mathlib only.
-/

namespace OpenAI086

/-- Difference of products, valid over the complex field. -/
theorem triple_difference_identity
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℂ) :
    a₀ * a₁ * a₂ - b₀ * b₁ * b₂ =
      (a₀ - b₀) * a₁ * a₂ +
      b₀ * (a₁ - b₁) * a₂ +
      b₀ * b₁ * (a₂ - b₂) := by
  ring

/-- The three-factor product difference admits a quantitative bound
in terms of the differences of individual factors. -/
theorem triple_difference_norm_bound
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℂ) :
    ‖a₀ * a₁ * a₂ - b₀ * b₁ * b₂‖ ≤
      ‖a₀ - b₀‖ * ‖a₁‖ * ‖a₂‖ +
      ‖b₀‖ * ‖a₁ - b₁‖ * ‖a₂‖ +
      ‖b₀‖ * ‖b₁‖ * ‖a₂ - b₂‖ := by
  rw [triple_difference_identity]
  calc
    ‖(a₀ - b₀) * a₁ * a₂ + b₀ * (a₁ - b₁) * a₂ +
        b₀ * b₁ * (a₂ - b₂)‖ ≤
      ‖(a₀ - b₀) * a₁ * a₂ + b₀ * (a₁ - b₁) * a₂‖ +
        ‖b₀ * b₁ * (a₂ - b₂)‖ := norm_add_le _ _
    _ ≤ (‖(a₀ - b₀) * a₁ * a₂‖ + ‖b₀ * (a₁ - b₁) * a₂‖) +
        ‖b₀ * b₁ * (a₂ - b₂)‖ :=
      add_le_add_right (norm_add_le _ _) _
    _ = ‖a₀ - b₀‖ * ‖a₁‖ * ‖a₂‖ +
          ‖b₀‖ * ‖a₁ - b₁‖ * ‖a₂‖ +
          ‖b₀‖ * ‖b₁‖ * ‖a₂ - b₂‖ := by
      simp only [norm_mul]

/-- Numerator after pairing the two sides of a symmetric singular integral.
There is no division by `t` here, so the expression is defined at zero. -/
def symmetricTripleNumerator
    (f : Fin 3 → ℝ → ℂ) (x t : ℝ) : ℂ :=
  f 0 (x - t) * f 1 (x - 2 * t) * f 2 (x - 3 * t) -
  f 0 (x + t) * f 1 (x + 2 * t) * f 2 (x + 3 * t)

/-- Exact cancellation at the singular point, with no hypotheses on `f`. -/
theorem symmetricTripleNumerator_at_zero
    (f : Fin 3 → ℝ → ℂ) (x : ℝ) :
    symmetricTripleNumerator f x 0 = 0 := by
  simp [symmetricTripleNumerator]

/-- Splitting the symmetrized numerator into three first differences. -/
theorem symmetricTripleNumerator_telescope
    (f : Fin 3 → ℝ → ℂ) (x t : ℝ) :
    symmetricTripleNumerator f x t =
      (f 0 (x - t) - f 0 (x + t)) *
        f 1 (x - 2 * t) * f 2 (x - 3 * t) +
      f 0 (x + t) * (f 1 (x - 2 * t) - f 1 (x + 2 * t)) *
        f 2 (x - 3 * t) +
      f 0 (x + t) * f 1 (x + 2 * t) *
        (f 2 (x - 3 * t) - f 2 (x + 3 * t)) := by
  unfold symmetricTripleNumerator
  ring

/-- Quantitative numerator estimate. Applying the mean-value inequality
to the three differences gives the local `O(|t|)` cancellation needed
for principal-value convergence of Schwartz inputs. -/
theorem symmetricTripleNumerator_bound
    (f : Fin 3 → ℝ → ℂ) (x t : ℝ) :
    ‖symmetricTripleNumerator f x t‖ ≤
      ‖f 0 (x - t) - f 0 (x + t)‖ *
        ‖f 1 (x - 2 * t)‖ * ‖f 2 (x - 3 * t)‖ +
      ‖f 0 (x + t)‖ *
        ‖f 1 (x - 2 * t) - f 1 (x + 2 * t)‖ *
        ‖f 2 (x - 3 * t)‖ +
      ‖f 0 (x + t)‖ * ‖f 1 (x + 2 * t)‖ *
        ‖f 2 (x - 3 * t) - f 2 (x + 3 * t)‖ := by
  unfold symmetricTripleNumerator
  exact triple_difference_norm_bound
    (f 0 (x - t)) (f 1 (x - 2 * t)) (f 2 (x - 3 * t))
    (f 0 (x + t)) (f 1 (x + 2 * t)) (f 2 (x + 3 * t))

end OpenAI086
