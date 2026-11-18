import Mathlib
import OpenAI086.SignConvention

/-!
# Algebraic symmetrization of the integrand in OpenAI #086

Unlike a principal-value theorem, these are identities of scalar kernels.
No measure-theoretic change of variables is asserted in this file.
-/

namespace OpenAI086

/-- Pairing `t` and `-t` removes the odd denominator and yields the
correct difference of two threefold shifted products. This is a pointwise
identity, valid even at `t=0` under Lean's total-field division. -/
theorem symmetric_kernel_pair (f : Fin 3 → ℝ → ℂ) (x t : ℝ) :
    kernelMinus f x t + kernelMinus f x (-t) =
      (f 0 (x-t) * f 1 (x-2*t) * f 2 (x-3*t) -
       f 0 (x+t) * f 1 (x+2*t) * f 2 (x+3*t)) / (t : ℂ) := by
  rw [kernel_reversal]
  simp only [kernelMinus, kernelPlus]
  ring

end OpenAI086
