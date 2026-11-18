import Mathlib

/-!
# OpenAI #086, §1–2: pointwise sign convention for t ↦ -t

The PDF defines its transform using `x-t,x-2t,x-3t`; parts of its proof
use the plus progression.  The kernel changes by a global minus sign
under `t ↦ -t`.  This file establishes the *pointwise algebraic identity*.
The associated integral change-of-variables statement is NOT proved here.
-/

namespace OpenAI086

noncomputable section

/-- The minus-shift kernel with a denominator `t`. -/
def kernelMinus (f : Fin 3 → ℝ → ℂ) (x t : ℝ) : ℂ :=
  (f 0 (x-t) * f 1 (x-2*t) * f 2 (x-3*t)) / (t : ℂ)

/-- The plus-shift kernel with a denominator `t`. -/
def kernelPlus (f : Fin 3 → ℝ → ℂ) (x t : ℝ) : ℂ :=
  (f 0 (x+t) * f 1 (x+2*t) * f 2 (x+3*t)) / (t : ℂ)

/-- Exact algebraic identity after reversing the integration parameter.
At the integral level this must be combined with measure invariance. -/
theorem kernel_reversal (f : Fin 3 → ℝ → ℂ) (x t : ℝ) :
    kernelMinus f x (-t) = -kernelPlus f x t := by
  have h0 : x - -t = x + t := by ring
  have h1 : x - 2*(-t) = x + 2*t := by ring
  have h2 : x - 3*(-t) = x + 3*t := by ring
  simp [kernelMinus, kernelPlus, h0, h1, h2]

end
end OpenAI086
