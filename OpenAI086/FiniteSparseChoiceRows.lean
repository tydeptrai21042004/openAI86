import Mathlib
import OpenAI086.FiniteLemma33Coarse
import OpenAI086.FiniteAdaptiveRowBessel

/-!
# Lemma 3.3: sparse-choice, variable-depth noncommuting rows

Unlike the older coarse estimate, which loses T+1, this theorem loses
only the number K of DISTINCT candidate depths available to the rows.
Each row is allowed its own selected depth among those K, and all m
projection layers may be noncommuting.  The result is independent of the
size of the actual depth indices and of the number of rows.

It is not the logarithmic bound in Lemma 3.3 when all T+1 depths can be
chosen: the dyadic orthogonality across depth choices remains open.
-/

namespace OpenAI086

/-- Bessel rows with K possible projection depths suffer only a K
energy loss, even when the depths themselves are arbitrarily large and
each of the m projection layers is noncommuting with the others. -/
theorem finite_sparse_choice_noncommuting_row_bound
    {d rows K : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (B : Fin rows → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Fin rows, (B r y) ^ 2) ≤ finiteRealPair y y)
    (levels : Fin K → ℕ) (choice : Fin rows → Fin K)
    (m : ℕ) (x : Fin d → ℝ) :
    (∑ r : Fin rows,
      (B r (finiteSequentialProjectionProduct P m (levels (choice r)) x)) ^ 2) ≤
        (K : ℝ) * finiteRealPair x x := by
  let signal : Fin K → Fin d → ℝ := fun k =>
    finiteSequentialProjectionProduct P m (levels k) x
  have hblock :
      (∑ k : Fin K, finiteRealPair (signal k) (signal k)) ≤
        (K : ℝ) * finiteRealPair x x := by
    calc
      (∑ k : Fin K, finiteRealPair (signal k) (signal k)) ≤
          ∑ _k : Fin K, finiteRealPair x x := by
        apply Finset.sum_le_sum
        intro k _
        exact finite_projection_foldl_energy P hsym hidemp
          (List.range m) (levels k) x
      _ = (K : ℝ) * finiteRealPair x x := by simp
  exact finite_adaptive_row_bessel
    (fun r y => B r y) signal choice
    ((K : ℝ) * finiteRealPair x x) hrow hblock

end OpenAI086
