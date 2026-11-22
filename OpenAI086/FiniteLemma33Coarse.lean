import Mathlib
import OpenAI086.FiniteLemma33Endpoints

/-!
# Unconditional coarse bounds for the *variable-prefix* finite model

These estimates apply to arbitrarily many ordered, noncommuting
self-adjoint idempotent operators and row-dependent prefix indices.
They are much weaker than Lemma 3.3: the manuscript needs a logarithmic
loss, whereas the row estimate below loses the number of depth levels.
The square-variation estimate also loses a factor proportional to depth.
The losses are stated explicitly so these cannot be confused with the
numbered manuscript lemma.
-/

namespace OpenAI086

/-- Even when the rows choose different projection depths, there is a
basic bound with a *linear depth loss*.  The proof groups rows by their
chosen index and uses the Bessel hypothesis once per index. -/
theorem finite_noncommuting_row_prefix_coarse
    {d rows : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (B : Fin rows → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Fin rows, (B r y) ^ 2) ≤ finiteRealPair y y)
    (m T : ℕ) (choice : Fin rows → Fin (T + 1))
    (x : Fin d → ℝ) :
    (∑ r : Fin rows,
      (B r (finiteSequentialProjectionProduct P m (choice r).val x)) ^ 2) ≤
      (T + 1 : ℕ) * finiteRealPair x x := by
  classical
  have hchoose (r : Fin rows) :
      (∑ k : Fin (T + 1),
        if k = choice r then
          (B r (finiteSequentialProjectionProduct P m k.val x)) ^ 2 else 0) =
      (B r (finiteSequentialProjectionProduct P m (choice r).val x)) ^ 2 := by
    simp
  calc
    (∑ r : Fin rows,
      (B r (finiteSequentialProjectionProduct P m (choice r).val x)) ^ 2) =
        ∑ r : Fin rows, ∑ k : Fin (T + 1),
          if k = choice r then
            (B r (finiteSequentialProjectionProduct P m k.val x)) ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro r _
              exact (hchoose r).symm
    _ = ∑ k : Fin (T + 1), ∑ r : Fin rows,
          if k = choice r then
            (B r (finiteSequentialProjectionProduct P m k.val x)) ^ 2 else 0 := by
              rw [Finset.sum_comm]
    _ ≤ ∑ k : Fin (T + 1), ∑ r : Fin rows,
          (B r (finiteSequentialProjectionProduct P m k.val x)) ^ 2 := by
            apply Finset.sum_le_sum
            intro k _
            apply Finset.sum_le_sum
            intro r _
            by_cases h : k = choice r
            · simp [h]
            · simp [h, sq_nonneg]
    _ ≤ ∑ _k : Fin (T + 1), finiteRealPair x x := by
          apply Finset.sum_le_sum
          intro k _
          exact finite_common_prefix_noncommuting_row_bessel
            P hsym hidemp B hrow m k.val x
    _ = (T + 1 : ℕ) * finiteRealPair x x := by simp

/-- Elementary energy inequality used to obtain an explicit, but
non-optimal, square-variation bound for ordered products. -/
theorem finite_pair_difference_le_twice {d : ℕ}
    (u v : Fin d → ℝ) :
    finiteRealPair (u - v) (u - v) ≤
      2 * (finiteRealPair u u + finiteRealPair v v) := by
  unfold finiteRealPair
  have hstep :
      (∑ i : Fin d, (u i - v i) * (u i - v i)) ≤
      ∑ i : Fin d, 2 * (u i * u i + v i * v i) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (u i + v i)]
  calc
    (∑ i : Fin d, (u - v) i * (u - v) i) =
        ∑ i : Fin d, (u i - v i) * (u i - v i) := by
          simp only [Pi.sub_apply]
    _ ≤ ∑ i : Fin d, 2 * (u i * u i + v i * v i) := hstep
    _ = 2 * ((∑ i : Fin d, u i * u i) +
          (∑ i : Fin d, v i * v i)) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib]

/-- At arbitrary depth the variation is bounded, with a loss of `4T`.
The logarithmic saving required by the manuscript is not yet present. -/
theorem finite_noncommuting_variation_coarse
    {d : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (m T : ℕ) (x : Fin d → ℝ) :
    (∑ n ∈ Finset.range T,
      finiteRealPair
        (finiteSequentialProjectionProduct P m (n + 1) x -
         finiteSequentialProjectionProduct P m n x)
        (finiteSequentialProjectionProduct P m (n + 1) x -
         finiteSequentialProjectionProduct P m n x)) ≤
      (4 * T : ℕ) * finiteRealPair x x := by
  have hstep (n : ℕ) :
      finiteRealPair
        (finiteSequentialProjectionProduct P m (n + 1) x -
         finiteSequentialProjectionProduct P m n x)
        (finiteSequentialProjectionProduct P m (n + 1) x -
         finiteSequentialProjectionProduct P m n x) ≤
      4 * finiteRealPair x x := by
    have hdiff := finite_pair_difference_le_twice
      (finiteSequentialProjectionProduct P m (n + 1) x)
      (finiteSequentialProjectionProduct P m n x)
    have hnext := finite_projection_foldl_energy
      P hsym hidemp (List.range m) (n + 1) x
    have hprev := finite_projection_foldl_energy
      P hsym hidemp (List.range m) n x
    change finiteRealPair
      (finiteSequentialProjectionProduct P m (n + 1) x)
      (finiteSequentialProjectionProduct P m (n + 1) x) ≤
      finiteRealPair x x at hnext
    change finiteRealPair
      (finiteSequentialProjectionProduct P m n x)
      (finiteSequentialProjectionProduct P m n x) ≤
      finiteRealPair x x at hprev
    linarith
  calc
    (∑ n ∈ Finset.range T,
      finiteRealPair
        (finiteSequentialProjectionProduct P m (n + 1) x -
         finiteSequentialProjectionProduct P m n x)
        (finiteSequentialProjectionProduct P m (n + 1) x -
         finiteSequentialProjectionProduct P m n x)) ≤
        ∑ _n ∈ Finset.range T, 4 * finiteRealPair x x := by
          apply Finset.sum_le_sum
          intro n _
          exact hstep n
    _ = (4 * T : ℕ) * finiteRealPair x x := by
          simp
          ring

end OpenAI086
