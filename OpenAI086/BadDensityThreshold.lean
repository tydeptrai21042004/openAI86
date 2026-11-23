import Mathlib

/-!
# Lemma 8.6: a genuinely pointwise counting inequality

The floor-log mismatch in the paper is an INTEGER event. If either of
two nonnegative logarithmic gaps is nonzero, their sum is at least 1.
A second bad-height event occurs when the sum of two nonnegative
exceptional-label fractions exceeds beta. Its indicator is bounded by
the fraction divided by beta. This is the elementary pointwise step
needed before the two-axis counting theorem.

The connection from the manuscript's actual nested finite label sets
to these nonnegative integer gaps is a separate formalization task.
-/

namespace OpenAI086

/-- The indicator of the union of a positive integer gap and an
exceptional-density threshold is bounded by gap size plus normalized
exceptional density. This is sharp when one gap is 1 and u=v=0. -/
theorem integer_gap_or_density_bound
    (a b : ℕ) (u v beta : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hbeta : 0 < beta) :
    (if 0 < a + b ∨ beta < u + v then (1 : ℝ) else 0) ≤
      (a : ℝ) + (b : ℝ) + (u + v) / beta := by
  have hnonneg : 0 ≤ (u + v) / beta :=
    div_nonneg (add_nonneg hu hv) (le_of_lt hbeta)
  by_cases hgap : 0 < a + b
  · have hunit : (1 : ℝ) ≤ (a : ℝ) + (b : ℝ) := by
      have hn : 1 ≤ a + b := by omega
      exact_mod_cast hn
    simp only [if_pos (Or.inl hgap)]
    linarith
  · have hzero : a = 0 ∧ b = 0 := by omega
    rcases hzero with ⟨rfl, rfl⟩
    by_cases hdense : beta < u + v
    · have hstrict : 1 < (u + v) / beta :=
        (lt_div_iff₀ hbeta).2 (by linarith)
      simpa [hdense] using le_of_lt hstrict
    · simpa [hdense] using hnonneg

end OpenAI086
