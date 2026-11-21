import Mathlib
import OpenAI086.PairedKernelBound

/-!
# The O(|t|) hypothesis follows from global Lipschitz control

For a Schwartz input the factorwise Lipschitz and uniform-size bounds
follow from elementary differentiation and decay.  Here we prove the
exact intermediate implication, with the two global bounds given as
explicit hypotheses; no analytic assumptions are silently inferred.

It is independent of the external trilinear-HT formalization.
-/

namespace OpenAI086

noncomputable section

/-- The argument difference at slope 1 has absolute value `2*|t|`. -/
private theorem abs_shift_one (x t : ℝ) :
    |(x - t) - (x + t)| = 2 * |t| := by
  have h : (x - t) - (x + t) = -(2 * t) := by ring
  rw [h, abs_neg, abs_mul]
  norm_num

/-- Corresponding shift difference for slope 2. -/
private theorem abs_shift_two (x t : ℝ) :
    |(x - 2*t) - (x + 2*t)| = 4 * |t| := by
  have h : (x - 2*t) - (x + 2*t) = -(4 * t) := by ring
  rw [h, abs_neg, abs_mul]
  norm_num

/-- Corresponding shift difference for slope 3. -/
private theorem abs_shift_three (x t : ℝ) :
    |(x - 3*t) - (x + 3*t)| = 6 * |t| := by
  have h : (x - 3*t) - (x + 3*t) = -(6 * t) := by ring
  rw [h, abs_neg, abs_mul]
  norm_num

/-- A uniform estimate on the *paired* singular kernel, deduced from
bounded, globally Lipschitz factors. It is independent of the truncation
parameter, but does not assert global integrability in `t`. -/
theorem paired_kernel_bound_of_global_lipschitz
    (f : Fin 3 → ℝ → ℂ) (x t : ℝ)
    (M K₀ K₁ K₂ : ℝ)
    (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hsize : ∀ (i : Fin 3) (y : ℝ), ‖f i y‖ ≤ M)
    (hLip₀ : ∀ (y z : ℝ), ‖f 0 y - f 0 z‖ ≤ K₀ * |y - z|)
    (hLip₁ : ∀ (y z : ℝ), ‖f 1 y - f 1 z‖ ≤ K₁ * |y - z|)
    (hLip₂ : ∀ (y z : ℝ), ‖f 2 y - f 2 z‖ ≤ K₂ * |y - z|) :
    ‖pairedHilbertKernel f x t‖ ≤ (2*K₀ + 4*K₁ + 6*K₂) * M^2 := by
  have h₀ : ‖f 0 (x-t) - f 0 (x+t)‖ ≤ (2*K₀) * |t| := by
    calc
      _ ≤ K₀ * |(x-t) - (x+t)| := hLip₀ _ _
      _ = (2*K₀) * |t| := by rw [abs_shift_one]; ring
  have h₁ : ‖f 1 (x-2*t) - f 1 (x+2*t)‖ ≤ (4*K₁) * |t| := by
    calc
      _ ≤ K₁ * |(x-2*t) - (x+2*t)| := hLip₁ _ _
      _ = (4*K₁) * |t| := by rw [abs_shift_two]; ring
  have h₂ : ‖f 2 (x-3*t) - f 2 (x+3*t)‖ ≤ (6*K₂) * |t| := by
    calc
      _ ≤ K₂ * |(x-3*t) - (x+3*t)| := hLip₂ _ _
      _ = (6*K₂) * |t| := by rw [abs_shift_three]; ring
  exact pairedHilbertKernel_bound f x t M
    (2*K₀) (4*K₁) (6*K₂) hM
    (mul_nonneg (by norm_num) hK₀)
    (mul_nonneg (by norm_num) hK₁)
    (mul_nonneg (by norm_num) hK₂)
    (hsize 1 _) (hsize 2 _) (hsize 0 _) (hsize 1 _)
    h₀ h₁ h₂

end
end OpenAI086
