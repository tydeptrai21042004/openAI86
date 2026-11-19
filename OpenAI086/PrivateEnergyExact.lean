import Mathlib
import OpenAI086.PrivateCoordinates

/-!
# OpenAI #086, Lemma 3.2: pointwise private-coordinate Gram lower estimate

The paper's columns are `Φ_v = (φ_v, ε_v e_v)` with mutually orthogonal
private directions. In this finite real-coordinate model the full squared
energy is the squared physical sum plus the sum of private-coordinate
squares. The estimate below is an exact finite-dimensional consequence.
It is *not* the `L∞` operator bound for the local L² projection.
-/

namespace OpenAI086

/-- Pointwise squared norm of the finite column combination. -/
def columnSquaredEnergy {n : ℕ}
    (φ ε c : Fin n → ℝ) : ℝ :=
    (∑ i : Fin n, c i * φ i) ^ 2 +
      (∑ i : Fin n, (ε i * c i) ^ 2)

/-- The physical contribution cannot reduce the private-coordinate energy. -/
theorem private_energy_le_total {n : ℕ}
    (φ ε c : Fin n → ℝ) :
    (∑ i : Fin n, (ε i * c i) ^ 2) ≤
      columnSquaredEnergy φ ε c := by
  unfold columnSquaredEnergy
  nlinarith [sq_nonneg (∑ i : Fin n, c i * φ i)]

/-- Positive definiteness of the private-coordinate Gram form, with the
quantitative `D⁻¹` lower amplitude bound from Lemma 3.2. -/
theorem private_column_coercivity {n : ℕ}
    (φ ε c : Fin n → ℝ) (D : ℝ)
    (hD : 0 < D) (hε : ∀ i, 1 / D ≤ ε i) :
    (∑ i : Fin n, (c i / D) ^ 2) ≤
      columnSquaredEnergy φ ε c := by
  exact (private_energy_lower_bound ε c D hD hε).trans
    (private_energy_le_total φ ε c)

/-- A combination of finite columns with nonzero private amplitudes
vanishes only when all coefficients vanish. -/
theorem finite_columns_linear_independent_at_point {n : ℕ}
    (φ ε c : Fin n → ℝ) (hε : ∀ i, ε i ≠ 0)
    (hzero : ∀ i, ε i * c i = 0) :
    c = 0 := by
  funext i
  have hz : c i = 0 := (mul_eq_zero.mp (hzero i)).resolve_left (hε i)
  simpa using hz

end OpenAI086
