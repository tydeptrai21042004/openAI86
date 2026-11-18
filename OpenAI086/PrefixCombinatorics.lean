import Mathlib

/-!
# Independent finite prefix combinatorics (preparation for Lemma 3.3)

An exact split of a prefix into consecutive pieces. Dyadic decomposition,
Bessel inequalities and the logarithmic row estimate are NOT proved here.
-/

namespace OpenAI086

/-- Prefix sums split at any interior point, preserving order. -/
theorem finite_prefix_concat (u : ℕ → ℝ) (a b : ℕ) :
    (∑ k ∈ Finset.range (a + b), u k) =
      (∑ k ∈ Finset.range a, u k) +
      (∑ k ∈ Finset.range b, u (a + k)) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- A two-half dyadic split, at a fixed finite scale. -/
theorem finite_prefix_dyadic_halves (u : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), u k) =
      (∑ k ∈ Finset.range n, u k) +
      (∑ k ∈ Finset.range n, u (n + k)) := by
  simpa [two_mul] using finite_prefix_concat u n n

end OpenAI086
