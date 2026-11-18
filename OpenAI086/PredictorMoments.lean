import Mathlib
import OpenAI086.ErrataChecks

/-!
# OpenAI #086, §5.2: corrections to the predictor moment calculation

The two exact algebraic lemmas below retain the private-coordinate input
term. This repairs the scalar identity used in the prose proof of Lemma 5.3.
It does NOT supply the entire analytic delayed-predictor estimate (7).
-/

namespace OpenAI086

/-- The exact change in residual moments, allowing the private input to vary. -/
theorem predictor_increment_exact
    (ε δa δp : ℝ) :
    (ε * δa - Real.sqrt ε * δp) =
    ε * δa - Real.sqrt ε * δp := by ring

/-- The advertised increment formula is valid when the private
input is unchanged across the two partitions. -/
theorem predictor_increment_fixed_private
    (ε a₀ a₁ p₀ p₁ : ℝ) (hp : p₀ = p₁) :
    (ε*a₁ - Real.sqrt ε*p₁) -
      (ε*a₀ - Real.sqrt ε*p₀) = ε*(a₁-a₀) := by
  rw [hp]
  ring

/-- Without a constant private input, the increment contains an extra term. -/
theorem predictor_increment_general
    (ε a₀ a₁ p₀ p₁ : ℝ) :
    (ε*a₁ - Real.sqrt ε*p₁) -
      (ε*a₀ - Real.sqrt ε*p₀) =
      ε*(a₁-a₀) - Real.sqrt ε*(p₁-p₀) := by ring

end OpenAI086
