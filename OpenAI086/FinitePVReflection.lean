import Mathlib
import OpenAI086.SignConvention
import OpenAI086.SymmetricNumerator

/-!
# Exact finite symmetric-cutoff reflection: no analytic assumptions

This is a discrete identity corresponding to the parameter substitution
`t ↦ -t` in the manuscript's principal-value integral. It is valid for
ANY finite sample collection and ANY complex weights. It does not replace
proof of the continuous change-of-variable theorem or convergence.

No code or proof is imported from the Roos project.
-/

namespace OpenAI086

/-- Pairing `t` and `-t` changes the sign of the triple Hilbert kernel. -/
theorem kernel_pair_reflection (f : Fin 3 → ℝ → ℂ)
    (x t : ℝ) :
    kernelMinus f x t + kernelMinus f x (-t) =
      -(kernelPlus f x t + kernelPlus f x (-t)) := by
  have h₁ := kernel_reversal f x t
  have h₂ := kernel_reversal f x (-t)
  simp only [neg_neg] at h₂
  rw [h₂, h₁]
  abel

/-- Arbitrary finite symmetric sampling is compatible with the
operator sign change, even with heterogeneous complex weights. -/
theorem finite_paired_reflection (f : Fin 3 → ℝ → ℂ)
    (x : ℝ) (S : Finset ℝ) (weight : ℝ → ℂ) :
    (∑ t ∈ S, weight t *
      (kernelMinus f x t + kernelMinus f x (-t))) =
      -(∑ t ∈ S, weight t *
        (kernelPlus f x t + kernelPlus f x (-t))) := by
  calc
    (∑ t ∈ S, weight t *
        (kernelMinus f x t + kernelMinus f x (-t))) =
      ∑ t ∈ S, -(weight t *
        (kernelPlus f x t + kernelPlus f x (-t))) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [kernel_pair_reflection]
          ring
    _ = -(∑ t ∈ S, weight t *
          (kernelPlus f x t + kernelPlus f x (-t))) := by
          simp only [Finset.sum_neg_distrib]

end OpenAI086
