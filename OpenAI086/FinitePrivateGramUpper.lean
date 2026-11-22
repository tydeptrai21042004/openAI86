import Mathlib
import OpenAI086.FiniteRowCauchySchwarz
import OpenAI086.PrivateEnergyExact

/-!
# Lemma 3.2: two-sided quantitative finite private-column bounds

For finitely many real columns `Φᵢ = (φᵢ, εᵢ eᵢ)`, the full squared
energy is `(∑ cᵢ φᵢ)^2 + ∑ (εᵢ cᵢ)^2`.  The existing modules proved
its lower bound by private-coordinate coercivity.  We add an **upper**
Gram bound with the correct `D^3` factor under the manuscript's
pointwise column-size and along-path label-count budgets.

This is an exact finite real pointwise counterpart of the *coefficient*
part of Lemma 3.2; the spatially integrated local projection estimate
`‖P_{I,A} z‖∞ ≤ D^5 avg_I ‖z‖` remains unproved.
-/

namespace OpenAI086

/-- The squared private-coordinate energy is bounded by the product of
the coefficient energy and the sum of squared private amplitudes. -/
theorem private_energy_finite_upper {n : ℕ}
    (ε c : Fin n → ℝ) :
    (∑ i : Fin n, (ε i * c i) ^ 2) ≤
      (∑ i : Fin n, (c i) ^ 2) * (∑ i : Fin n, (ε i) ^ 2) := by
  classical
  have hsingle (i : Fin n) :
      (ε i) ^ 2 ≤ ∑ j : Fin n, (ε j) ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ _ => sq_nonneg (ε j)) (Finset.mem_univ i)
  calc
    (∑ i : Fin n, (ε i * c i) ^ 2) =
        ∑ i : Fin n, (c i) ^ 2 * (ε i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ ∑ i : Fin n, (c i) ^ 2 * (∑ j : Fin n, (ε j) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hsingle i) (sq_nonneg (c i))
    _ = (∑ i : Fin n, (c i) ^ 2) * (∑ i : Fin n, (ε i) ^ 2) := by
          rw [Finset.sum_mul]

/-- An upper Gram-energy bound for arbitrary finite private columns.
The private directions must be distinct but **no** orthogonality is
assumed of the physical scalar functions. -/
theorem finite_private_column_gram_upper {n : ℕ}
    (φ ε c : Fin n → ℝ) :
    columnSquaredEnergy φ ε c ≤
      (∑ i : Fin n, (c i) ^ 2) *
        (∑ i : Fin n, ((φ i) ^ 2 + (ε i) ^ 2)) := by
  have hphysical := finite_row_cauchy_schwarz c φ
  have hprivate := private_energy_finite_upper ε c
  unfold columnSquaredEnergy
  calc
    (∑ i : Fin n, c i * φ i) ^ 2 +
        (∑ i : Fin n, (ε i * c i) ^ 2) ≤
      (∑ i : Fin n, (c i) ^ 2) * (∑ i : Fin n, (φ i) ^ 2) +
        (∑ i : Fin n, (c i) ^ 2) * (∑ i : Fin n, (ε i) ^ 2) :=
          add_le_add hphysical hprivate
    _ = (∑ i : Fin n, (c i) ^ 2) *
        (∑ i : Fin n, ((φ i) ^ 2 + (ε i) ^ 2)) := by
          rw [Finset.sum_add_distrib]
          ring

/-- When at most `D` columns are active and every column has squared
norm at most `D²`, the upper coefficient bound is exactly `D³`. -/
theorem finite_private_column_upper_budget {n : ℕ}
    (φ ε c : Fin n → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hn : (n : ℝ) ≤ D)
    (hcol : ∀ i, (φ i) ^ 2 + (ε i) ^ 2 ≤ D ^ 2) :
    columnSquaredEnergy φ ε c ≤
      D ^ 3 * (∑ i : Fin n, (c i) ^ 2) := by
  have hsize :
      (∑ i : Fin n, ((φ i) ^ 2 + (ε i) ^ 2)) ≤ D ^ 3 := by
    calc
      (∑ i : Fin n, ((φ i) ^ 2 + (ε i) ^ 2)) ≤
        ∑ _i : Fin n, D ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact hcol i
      _ = (n : ℝ) * D ^ 2 := by simp
      _ ≤ D ^ 3 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg D)]
  have hcoeff : 0 ≤ ∑ i : Fin n, (c i) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg (c i)
  calc
    columnSquaredEnergy φ ε c ≤
      (∑ i : Fin n, (c i) ^ 2) *
        (∑ i : Fin n, ((φ i) ^ 2 + (ε i) ^ 2)) :=
          finite_private_column_gram_upper φ ε c
    _ ≤ (∑ i : Fin n, (c i) ^ 2) * D ^ 3 :=
          mul_le_mul_of_nonneg_left hsize hcoeff
    _ = D ^ 3 * (∑ i : Fin n, (c i) ^ 2) := by ring

/-- The exact finite real, pointwise two-sided coefficient estimate:
`D⁻²‖c‖² ≤ ‖∑ cᵢ Φᵢ‖² ≤ D³‖c‖²`. -/
theorem finite_private_column_two_sided {n : ℕ}
    (φ ε c : Fin n → ℝ) (D : ℝ)
    (hD : 0 < D) (hn : (n : ℝ) ≤ D)
    (hε : ∀ i, 1 / D ≤ ε i)
    (hcol : ∀ i, (φ i) ^ 2 + (ε i) ^ 2 ≤ D ^ 2) :
    (∑ i : Fin n, (c i / D) ^ 2) ≤ columnSquaredEnergy φ ε c ∧
      columnSquaredEnergy φ ε c ≤ D ^ 3 * (∑ i : Fin n, (c i) ^ 2) := by
  exact ⟨private_column_coercivity φ ε c D hD hε,
    finite_private_column_upper_budget φ ε c D (le_of_lt hD) hn hcol⟩

end OpenAI086
