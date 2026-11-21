import Mathlib
import OpenAI086.GlobalLipschitzCancellation

/-!
# Exact Schwartz -> uniform size bridge

Mathlib already provides seminorm bounds for Schwartz functions.  This
module records the elementary three-input consequence used in the
principal-value numerator estimate.  Only *size*, not the full global
Lipschitz and decay statements, is handled here.

No external formalization has been copied or imported.
-/

namespace OpenAI086

noncomputable section

/-- The zeroth Schwartz seminorm bounds each pointwise norm. -/
theorem schwartz_value_bounded_by_seminorm
    (g : SchwartzMap ℝ ℂ) (y : ℝ) :
    ‖g y‖ ≤ (SchwartzMap.seminorm ℝ 0 0) g := by
  exact SchwartzMap.norm_le_seminorm ℝ g y

/-- A single nonnegative size budget for three Schwartz inputs. -/
def tripleSchwartzSize (f : Fin 3 → SchwartzMap ℝ ℂ) : ℝ :=
  (SchwartzMap.seminorm ℝ 0 0) (f 0) +
  (SchwartzMap.seminorm ℝ 0 0) (f 1) +
  (SchwartzMap.seminorm ℝ 0 0) (f 2)

/-- Every factor is bounded by the same explicit three-input budget. -/
theorem tripleSchwartzSize_bound
    (f : Fin 3 → SchwartzMap ℝ ℂ) (i : Fin 3) (y : ℝ) :
    ‖f i y‖ ≤ tripleSchwartzSize f := by
  have h₀ := schwartz_value_bounded_by_seminorm (f 0) y
  have h₁ := schwartz_value_bounded_by_seminorm (f 1) y
  have h₂ := schwartz_value_bounded_by_seminorm (f 2) y
  have hn₀ : 0 ≤ (SchwartzMap.seminorm ℝ 0 0) (f 0) :=
    (norm_nonneg (f 0 y)).trans h₀
  have hn₁ : 0 ≤ (SchwartzMap.seminorm ℝ 0 0) (f 1) :=
    (norm_nonneg (f 1 y)).trans h₁
  have hn₂ : 0 ≤ (SchwartzMap.seminorm ℝ 0 0) (f 2) :=
    (norm_nonneg (f 2 y)).trans h₂
  fin_cases i <;> dsimp [tripleSchwartzSize] <;> linarith

/-- The common size budget is nonnegative. -/
theorem tripleSchwartzSize_nonneg (f : Fin 3 → SchwartzMap ℝ ℂ) :
    0 ≤ tripleSchwartzSize f := by
  have h := tripleSchwartzSize_bound f 0 0
  exact (norm_nonneg ((f 0) 0)).trans h

/-- Upper bound on all first derivatives is already available as a
Mathlib Schwartz seminorm.  The mean-value/Lipschitz transfer is still
an independent lemma to be supplied. -/
theorem schwartz_first_iterated_derivative_bound
    (g : SchwartzMap ℝ ℂ) (y : ℝ) :
    ‖iteratedFDeriv ℝ 1 (g : ℝ → ℂ) y‖ ≤
      (SchwartzMap.seminorm ℝ 0 1) g := by
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g 1 y

/-- An exact bridge from actual Schwartz inputs to the bounded paired
kernel, assuming the stated global Lipschitz estimates.  The remaining
Schwartz derivative -> Lipschitz implication is kept explicit rather than
claimed to have been proved here. -/
theorem paired_kernel_bound_for_schwartz_of_lipschitz
    (f : Fin 3 → SchwartzMap ℝ ℂ) (x t : ℝ)
    (K₀ K₁ K₂ : ℝ)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hLip₀ : ∀ (y z : ℝ), ‖f 0 y - f 0 z‖ ≤ K₀ * |y - z|)
    (hLip₁ : ∀ (y z : ℝ), ‖f 1 y - f 1 z‖ ≤ K₁ * |y - z|)
    (hLip₂ : ∀ (y z : ℝ), ‖f 2 y - f 2 z‖ ≤ K₂ * |y - z|) :
    ‖pairedHilbertKernel (fun i y => f i y) x t‖ ≤
       (2*K₀ + 4*K₁ + 6*K₂) * (tripleSchwartzSize f)^2 := by
  exact paired_kernel_bound_of_global_lipschitz
    (fun i y => f i y) x t (tripleSchwartzSize f)
    K₀ K₁ K₂ (tripleSchwartzSize_nonneg f) hK₀ hK₁ hK₂
    (fun i y => tripleSchwartzSize_bound f i y)
    hLip₀ hLip₁ hLip₂

end
end OpenAI086
