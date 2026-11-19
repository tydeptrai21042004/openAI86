import Mathlib
import OpenAI086.Packing

/-!
# OpenAI #086, §3.5: basic geometric tails underlying the height-bin lemma

The `height bins` lemma itself involves rational linear dependencies and
is NOT established by these elementary geometric estimates. This file
formalizes only the per-bin dyadic summation used at the end of its proof.
-/

namespace OpenAI086

/-- Partial sum of the dyadic geometric progression is bounded by 2. -/
theorem dyadic_geometric_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have h := geometric_sum_uniform (1 / 2 : ℝ) (by norm_num) (by norm_num) N
  norm_num at h ⊢
  exact h

/-- Analogous bound at squared dyadic scale. -/
theorem quadratic_dyadic_geometric_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 4 : ℝ) ^ n) ≤ 4 / 3 := by
  have h := geometric_sum_uniform (1 / 4 : ℝ) (by norm_num) (by norm_num) N
  norm_num at h ⊢
  exact h

/-- At every occupied dyadic magnitude bin the weighted tail has a
with a constant independent of the number of later scales. -/
theorem dyadic_tail_with_amplitude (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    (∑ n ∈ Finset.range N, ε * (1 / 2 : ℝ) ^ n) ≤ 2 * ε := by
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (dyadic_geometric_sum N) hε

/-- A finite family of bins incurs the cardinality factor: this is
the *geometric summation step*, not the rational-height bound on bins. -/
theorem dyadic_tail_multiple_bins (bins : Finset ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (N : ℕ) :
    (∑ _b ∈ bins, ∑ n ∈ Finset.range N, ε * (1 / 2 : ℝ) ^ n) ≤
      (bins.card : ℝ) * (2 * ε) := by
  calc
    (∑ _b ∈ bins, ∑ n ∈ Finset.range N, ε * (1 / 2 : ℝ) ^ n)
        ≤ ∑ _b ∈ bins, 2 * ε := by
            apply Finset.sum_le_sum
            intro b hb
            exact dyadic_tail_with_amplitude ε hε N
    _ = (bins.card : ℝ) * (2 * ε) := by simp

end OpenAI086
