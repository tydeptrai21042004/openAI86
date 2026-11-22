import Mathlib

/-!
# V6: endpoint variation over finite paths (manuscript Lemma 6.2)

A formal telescoping identity for arbitrarily long finite paths. The
paper needs much stronger frequency-parameter estimates; this lemma
models their algebraic path-sum backbone only.
-/

namespace OpenAI086

/-- The exact sum of consecutive edge differences equals the endpoint
difference, without requiring a nonnegative or monotone path. -/
theorem finite_path_difference_telescope
    (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (a (k + 1) - a k)) = a N - a 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A uniform bound on each edge gives a bound linear in path length.
In the paper the edge frequency errors also depend on scale and a
rational parameter budget, not represented here. -/
theorem finite_path_endpoint_bound
    (a : ℕ → ℝ) (K : ℝ) (N : ℕ) :
    (∀ k < N, |a (k + 1) - a k| ≤ K) →
      |a N - a 0| ≤ (N : ℝ) * K := by
  induction N with
  | zero => intro _; simp
  | succ N ih =>
      intro h
      have hprevious : ∀ k < N, |a (k + 1) - a k| ≤ K := by
        intro k hk
        exact h k (by omega)
      have hprev := ih hprevious
      have hlast := h N (by omega)
      have htriangle : |a (N + 1) - a 0| ≤
          |a (N + 1) - a N| + |a N - a 0| := by
        have heq : a (N + 1) - a 0 =
            (a (N + 1) - a N) + (a N - a 0) := by ring
        rw [heq]
        exact abs_add_le _ _
      calc
        |a (N + 1) - a 0| ≤
            |a (N + 1) - a N| + |a N - a 0| := htriangle
        _ ≤ K + (N : ℝ) * K := add_le_add hlast hprev
        _ = (N + 1 : ℕ) * K := by push_cast; ring

end OpenAI086
