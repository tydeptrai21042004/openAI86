import Mathlib

/-!
# OpenAI #086, Lemma 8.5: the independent rank-budget summation step

Paper Lemma 8.5 states a harmonic loss for increasing finite sets. This
module formalizes its EXACT double-counting summation after assigning an
entry rank and bounding each rank's weighted incidence. Construction of
entry ranks and deduction of those hypotheses from nested sets remain open.
-/

namespace OpenAI086

/-- Finite harmonic sum; `M` here is the cardinality of the final set. -/
def finiteHarmonic (M : ℕ) : ℝ :=
  ∑ r ∈ Finset.range M, (1 : ℝ) / ((r + 1 : ℕ) : ℝ)

/-- Summing rank contributions incurs exactly the harmonic factor.
The hypothesis captures the per-element incidence estimate derived from
the first-entry enumeration, and is not claimed to follow automatically. -/
theorem entry_rank_double_count
    (T M : ℕ) (A : ℝ) (w : Fin T → Fin M → ℝ)
    (hrank : ∀ r : Fin M,
      (∑ t : Fin T, w t r) ≤ A / (((r.val + 1 : ℕ) : ℝ))) :
    (∑ t : Fin T, ∑ r : Fin M, w t r) ≤
      A * (∑ r : Fin M, (1 : ℝ) / (((r.val + 1 : ℕ) : ℝ))) := by
  calc
    (∑ t : Fin T, ∑ r : Fin M, w t r) =
        ∑ r : Fin M, ∑ t : Fin T, w t r := by rw [Finset.sum_comm]
    _ ≤ ∑ r : Fin M, A / (((r.val + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hrank r
    _ = A * (∑ r : Fin M, (1 : ℝ) / (((r.val + 1 : ℕ) : ℝ))) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, mul_one, one_mul]

end OpenAI086
