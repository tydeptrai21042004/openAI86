import Mathlib
import OpenAI086.Resonance

/-!
# OpenAI #086, Introduction: cancellation of matched quadratic phases

For real quadratic `q(z) = λ*z^2 + β*z + γ`, a four-slot phase with
coefficients `(-1,3,-3,1)` vanishes along `x,x+t,x+2t,x+3t`.
The exact complex exponential invariance then follows algebraically from
this identity, but is not needed for the norm estimate by itself.
-/

namespace OpenAI086

/-- Matched real polynomial phases of degree at most two cancel. -/
theorem matched_quadratic_phase
    (λ β γ x t : ℝ) :
    -(λ*x^2+β*x+γ) +
      3*(λ*(x+t)^2+β*(x+t)+γ) -
      3*(λ*(x+2*t)^2+β*(x+2*t)+γ) +
      (λ*(x+3*t)^2+β*(x+3*t)+γ) = 0 := by
  ring

/-- A product with four matched real exponential phases has total phase
zero (a *phase* statement, not an operator-norm statement). -/
theorem matched_phase_exponential (λ β γ x t : ℝ) :
    Complex.exp (((-(λ*x^2+β*x+γ) +
      3*(λ*(x+t)^2+β*(x+t)+γ) -
      3*(λ*(x+2*t)^2+β*(x+2*t)+γ) +
      (λ*(x+3*t)^2+β*(x+3*t)+γ) : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [matched_quadratic_phase]
  simp

end OpenAI086
