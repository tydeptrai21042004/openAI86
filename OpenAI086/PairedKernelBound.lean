import Mathlib
import OpenAI086.SymmetricLocalCancellation

/-!
# Uniform control of the symmetrized kernel near t = 0

After pairing the positive and negative halves of the principal value,
its integrand is the quotient of `symmetricTripleNumerator` by `t`.
The previously formalized O(|t|) bound therefore cancels the singular
factor pointwise.  This is an elementary *local* lemma and does not prove
measurability, integrability, or the full trilinear L^3 bound.

Independent derivation; no external Lean source is imported.
-/

namespace OpenAI086

noncomputable section

/-- The paired kernel, with the totalized convention at `t = 0`. -/
def pairedHilbertKernel (f : Fin 3 → ℝ → ℂ) (x t : ℝ) : ℂ :=
  symmetricTripleNumerator f x t / (t : ℂ)

/-- At the singular point the paired kernel is assigned the value zero. -/
theorem pairedHilbertKernel_zero (f : Fin 3 → ℝ → ℂ) (x : ℝ) :
    pairedHilbertKernel f x 0 = 0 := by
  simp [pairedHilbertKernel, symmetricTripleNumerator_at_zero]

/-- A general quotient principle: O(|t|) cancellation removes the 1/t
singularity pointwise, for every nonzero real `t`. -/
theorem quotient_bounded_of_linear_vanishing
    (g : ℝ → ℂ) (B t : ℝ) (ht : t ≠ 0)
    (hbound : ‖g t‖ ≤ B * |t|) :
    ‖g t / (t : ℂ)‖ ≤ B := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have hquot : ‖g t‖ / |t| ≤ B :=
    (div_le_iff₀ habs).2 hbound
  simpa only [norm_div, Complex.norm_real] using hquot

/-- A global version, including the value at zero. -/
theorem quotient_bounded_at_zero_of_linear_vanishing
    (g : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hzero : g 0 = 0)
    (hbound : ∀ t : ℝ, ‖g t‖ ≤ B * |t|) :
    ∀ t : ℝ, ‖g t / (t : ℂ)‖ ≤ B := by
  intro t
  by_cases ht : t = 0
  · subst t
    simp [hzero, hB]
  · exact quotient_bounded_of_linear_vanishing g B t ht (hbound t)

/-- Exact application to the trilinear symmetrized kernel under the
explicit local size and difference hypotheses of the preceding module. -/
theorem pairedHilbertKernel_bound
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
    ‖pairedHilbertKernel f x t‖ ≤ (L₀ + L₁ + L₂) * M ^ 2 := by
  let B : ℝ := (L₀ + L₁ + L₂) * M ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  by_cases ht : t = 0
  · subst t
    simpa only [pairedHilbertKernel_zero, norm_zero] using hB
  · have hnumerator :
        ‖symmetricTripleNumerator f x t‖ ≤ B * |t| := by
        simpa [B, mul_assoc] using
          (symmetric_numerator_linear_bound f x t M L₀ L₁ L₂
            hM hL₀ hL₁ hL₂ ha₁ ha₂ hb₀ hb₁ h₀ h₁ h₂)
    exact quotient_bounded_of_linear_vanishing
      (symmetricTripleNumerator f x) B t ht hnumerator

end
end OpenAI086
