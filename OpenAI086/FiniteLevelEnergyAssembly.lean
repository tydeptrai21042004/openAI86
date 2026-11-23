import Mathlib
import OpenAI086.FiniteRowCauchySchwarz

/-!
# Lemma 3.3: assembling dyadic LEVEL estimates with the logarithmic cost

For each fixed binary-block *length*, the row-Bessel argument in the
paper produces one squared-energy bound.  After summing the at most
`L_T` lengths, the Rademacher–Menshov step costs `L_T²` in squared
energy. This file proves that purely quantitative assembly in finite
real Hilbert coordinates; the blockwise Bessel premise must still be
proved for the actual nested orthogonal projection differences.

These are independent proof candidates, not a claim that Lemma 3.3 or
its noncommuting m-layer generalization has been established.
-/

namespace OpenAI086

/-- Assemble a uniform bound `E` for each fixed level into an `L² E`
bound for a sum of `L` levels in every row.  This step itself requires
no projection or linear-operator hypotheses. -/
theorem finite_scalar_level_energy_assembly
    {Row Level : Type*} [Fintype Row] [Fintype Level]
    (a : Row → Level → ℝ) (E : ℝ)
    (hlevel : ∀ ell : Level,
      (∑ r : Row, (a r ell) ^ 2) ≤ E) :
    (∑ r : Row, (∑ ell : Level, a r ell) ^ 2) ≤
      ((Fintype.card Level : ℕ) : ℝ) ^ 2 * E := by
  classical
  have hrow (r : Row) :
      (∑ ell : Level, a r ell) ^ 2 ≤
        ((Fintype.card Level : ℕ) : ℝ) *
          (∑ ell : Level, (a r ell) ^ 2) := by
    have hc := finite_row_cauchy_schwarz
      (a r) (fun _ : Level => (1 : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  have hsum :
      (∑ r : Row, (∑ ell : Level, a r ell) ^ 2) ≤
        ∑ r : Row, ((Fintype.card Level : ℕ) : ℝ) *
          (∑ ell : Level, (a r ell) ^ 2) := by
    apply Finset.sum_le_sum
    intro r _
    exact hrow r
  have hperlevel :
      (∑ ell : Level, ∑ r : Row, (a r ell) ^ 2) ≤
      (∑ _ell : Level, E) := by
    apply Finset.sum_le_sum
    intro ell _
    exact hlevel ell
  calc
    (∑ r : Row, (∑ ell : Level, a r ell) ^ 2) ≤
        ∑ r : Row, ((Fintype.card Level : ℕ) : ℝ) *
          (∑ ell : Level, (a r ell) ^ 2) := hsum
    _ = ((Fintype.card Level : ℕ) : ℝ) *
          (∑ r : Row, ∑ ell : Level, (a r ell) ^ 2) := by
            rw [Finset.mul_sum]
    _ = ((Fintype.card Level : ℕ) : ℝ) *
          (∑ ell : Level, ∑ r : Row, (a r ell) ^ 2) := by
            rw [Finset.sum_comm]
    _ ≤ ((Fintype.card Level : ℕ) : ℝ) *
          (∑ _ell : Level, E) :=
          mul_le_mul_of_nonneg_left hperlevel (by positivity)
    _ = ((Fintype.card Level : ℕ) : ℝ) ^ 2 * E := by
          simp only [Finset.sum_const_zero, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring

/-- Apply the preceding level-assembly lemma to actual REAL-LINEAR
row maps. The row index may choose different block operators within
any given level. The yet-open step in Lemma 3.3 is proving `hlevel`
from the dyadic orthogonality of *nested projection increments*. -/
theorem finite_linear_level_energy_assembly
    {d : ℕ} {Row Level : Type*}
    [Fintype Row] [Fintype Level]
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (Q : Row → Level → (Fin d → ℝ)) (E : ℝ)
    (hlevel : ∀ ell : Level,
      (∑ r : Row, (B r (Q r ell)) ^ 2) ≤ E) :
    (∑ r : Row, (B r (∑ ell : Level, Q r ell)) ^ 2) ≤
      ((Fintype.card Level : ℕ) : ℝ) ^ 2 * E := by
  classical
  have h := finite_scalar_level_energy_assembly
    (fun r ell => B r (Q r ell)) E hlevel
  simpa only [map_sum] using h

end OpenAI086
