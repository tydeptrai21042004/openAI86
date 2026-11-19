import Mathlib
import OpenAI086.UniformBootstrap

/-!
# OpenAI #086, §2: four-family stopping loss and abstract absorption

These statements formalize the numerical packing constants in the proof of
Lemma 2.4 (paper pp. 4–5). The actual maximal-function stopping algorithm,
local form estimate, and trilinear singular integral are not proved here.
No analytic estimate is silently assumed.
-/

namespace OpenAI086

/-- If each of four disjoint-or-overlapping exceptional families costs at
most one sixteenth of the parent, their *union* costs at most one quarter.
The hypothesis uses an upper bound for the mass of each family, so this
also applies without disjointness by subadditivity. -/
theorem four_stopping_families_bound
    (root s₀ s₁ s₂ s₃ : ℝ)
    (h₀ : s₀ ≤ root / 16)
    (h₁ : s₁ ≤ root / 16)
    (h₂ : s₂ ≤ root / 16)
    (h₃ : s₃ ≤ root / 16) :
    s₀ + s₁ + s₂ + s₃ ≤ root / 4 := by
  linarith

/-- Quantitative good-set lower bound `|E_J| ≥ 3|J|/4` in Lemma 2.4.
Only the measure-accounting implication, not the measurable set
construction, is asserted. -/
theorem good_root_retains_three_quarters
    (root s₀ s₁ s₂ s₃ : ℝ)
    (h₀ : s₀ ≤ root / 16)
    (h₁ : s₁ ≤ root / 16)
    (h₂ : s₂ ≤ root / 16)
    (h₃ : s₃ ≤ root / 16) :
    3 * root / 4 ≤ root - (s₀ + s₁ + s₂ + s₃) := by
  have h := four_stopping_families_bound root s₀ s₁ s₂ s₃ h₀ h₁ h₂ h₃
  linarith

/-- The normalized inequality `C_N ≤ A + c C_N` implies a uniform bound,
provided the analytic estimate has already been obtained. -/
theorem normalized_absorption_all_depths
    (C : ℕ → ℝ) (A c : ℝ)
    (hc : c < 1)
    (hestimate : ∀ N, C N ≤ A + c * C N) :
    ∀ N, C N ≤ A / (1 - c) := by
  exact uniform_absorption C A c hc hestimate

/-- Useful concrete parameter choice: `c ≤ 1/2` gives `C_N ≤ 2A`
when `A ≥ 0` and the one-depth estimate is available. -/
theorem half_absorption_bound
    (A C c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h : C ≤ A + c * C) :
    C ≤ 2 * A := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hC]

end OpenAI086
