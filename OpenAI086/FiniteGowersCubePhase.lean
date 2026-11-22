import Mathlib

/-!
# V6: exact third differences of polynomial phases (Section 4.8)

The degree-two Gowers-cube resonance is a fundamental algebraic feature
of the manuscript's quadratic phases.  These are exact real identities.
They do not prove the U³ seminorm estimate or the quantitative inverse
theorem of Section 4.
-/

namespace OpenAI086

/-- Alternating third additive difference on a 3-dimensional cube. -/
def finiteThirdDifference (f : ℝ → ℝ)
    (x h₁ h₂ h₃ : ℝ) : ℝ :=
  f (x + h₁ + h₂ + h₃) -
  f (x + h₁ + h₂) -
  f (x + h₁ + h₃) -
  f (x + h₂ + h₃) +
  f (x + h₁) + f (x + h₂) + f (x + h₃) - f x

/-- All quadratic phases vanish under the third alternating cube
difference, regardless of the four real coefficients and shifts. -/
theorem finite_quadratic_cube_third_difference_zero
    (lambda beta gamma x h₁ h₂ h₃ : ℝ) :
    finiteThirdDifference (fun y => lambda * y ^ 2 + beta * y + gamma)
      x h₁ h₂ h₃ = 0 := by
  unfold finiteThirdDifference
  ring

/-- Cubic phases do not generally vanish: their third difference is
the exact interaction term `6 h₁ h₂ h₃`. This distinguishes the
quadratic resonance from a generic degree-three modulation. -/
theorem finite_cubic_cube_third_difference
    (x h₁ h₂ h₃ : ℝ) :
    finiteThirdDifference (fun y => y ^ 3) x h₁ h₂ h₃ =
      6 * h₁ * h₂ * h₃ := by
  unfold finiteThirdDifference
  ring

end OpenAI086
