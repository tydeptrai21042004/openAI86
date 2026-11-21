import Mathlib
import OpenAI086.SymmetricNumerator

/-!
# Independent quantitative cancellation at the singularity

This formalizes the *local estimate* behind the principal-value existence
argument in §2 of the manuscript. Given explicit local bounds on the three
factors and their first differences, the symmetric numerator is O(|t|).

It does not claim that the full trilinear Hilbert transform is bounded.
No code from an external formalization has been copied or imported.
-/

namespace OpenAI086

/-- A general three-factor difference estimate under a common size bound
and (possibly distinct) moduli for the individual differences. -/
theorem triple_difference_common_majorant
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℂ)
    (M d₀ d₁ d₂ : ℝ)
    (hM : 0 ≤ M) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (ha₁ : ‖a₁‖ ≤ M) (ha₂ : ‖a₂‖ ≤ M)
    (hb₀ : ‖b₀‖ ≤ M) (hb₁ : ‖b₁‖ ≤ M)
    (h₀ : ‖a₀ - b₀‖ ≤ d₀)
    (h₁ : ‖a₁ - b₁‖ ≤ d₁)
    (h₂ : ‖a₂ - b₂‖ ≤ d₂) :
    ‖a₀ * a₁ * a₂ - b₀ * b₁ * b₂‖ ≤ (d₀ + d₁ + d₂) * M ^ 2 := by
  calc
    ‖a₀ * a₁ * a₂ - b₀ * b₁ * b₂‖ ≤
        ‖a₀ - b₀‖ * ‖a₁‖ * ‖a₂‖ +
        ‖b₀‖ * ‖a₁ - b₁‖ * ‖a₂‖ +
        ‖b₀‖ * ‖b₁‖ * ‖a₂ - b₂‖ :=
      triple_difference_norm_bound a₀ a₁ a₂ b₀ b₁ b₂
    _ ≤ d₀ * M * M + M * d₁ * M + M * M * d₂ := by
      gcongr <;> assumption
    _ = (d₀ + d₁ + d₂) * M ^ 2 := by ring

/-- Explicit local linear cancellation for the symmetric trilinear
numerator at any `x,t`, assuming factor bounds and linear first differences.
For differentiable Schwartz inputs these assumptions follow locally from
bounded derivatives; that analytic implication is a separate obligation. -/
theorem symmetric_numerator_linear_bound
    (f : Fin 3 → ℝ → ℂ) (x t : ℝ)
    (M L₀ L₁ L₂ : ℝ)
    (hM : 0 ≤ M) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (ha₁ : ‖f 1 (x - 2 * t)‖ ≤ M)
    (ha₂ : ‖f 2 (x - 3 * t)‖ ≤ M)
    (hb₀ : ‖f 0 (x + t)‖ ≤ M)
    (hb₁ : ‖f 1 (x + 2 * t)‖ ≤ M)
    (h₀ : ‖f 0 (x - t) - f 0 (x + t)‖ ≤ L₀ * |t|)
    (h₁ : ‖f 1 (x - 2 * t) - f 1 (x + 2 * t)‖ ≤ L₁ * |t|)
    (h₂ : ‖f 2 (x - 3 * t) - f 2 (x + 3 * t)‖ ≤ L₂ * |t|) :
    ‖symmetricTripleNumerator f x t‖ ≤
      (L₀ + L₁ + L₂) * M ^ 2 * |t| := by
  unfold symmetricTripleNumerator
  have h := triple_difference_common_majorant
    (f 0 (x - t)) (f 1 (x - 2 * t)) (f 2 (x - 3 * t))
    (f 0 (x + t)) (f 1 (x + 2 * t)) (f 2 (x + 3 * t))
    M (L₀ * |t|) (L₁ * |t|) (L₂ * |t|)
    hM (mul_nonneg hL₀ (abs_nonneg t))
    (mul_nonneg hL₁ (abs_nonneg t))
    (mul_nonneg hL₂ (abs_nonneg t))
    ha₁ ha₂ hb₀ hb₁ h₀ h₁ h₂
  calc
    _ ≤ (L₀ * |t| + L₁ * |t| + L₂ * |t|) * M ^ 2 := h
    _ = (L₀ + L₁ + L₂) * M ^ 2 * |t| := by ring

end OpenAI086
