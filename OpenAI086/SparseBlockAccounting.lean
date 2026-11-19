import Mathlib
import OpenAI086.SparsePairBudget

/-!
# OpenAI #086, Lemma 9.1, p. 83: numerical counting-block accounting

The paper greedily groups scales of mass at most `δ*M²` into blocks
of mass at most `α*M²`. Every nonterminal block exceeds
`(α-δ)*M²` and the total mass is bounded by `L*M²`.

This module proves the resulting **conditional** numerical bound on
block count, independent of the number of original scales.  The
algorithm constructing the greedy blocks remains to be formalized.
-/

namespace OpenAI086

/-- From a total mass budget and a positive lower mass on all but the
last block, derive a uniform upper bound on the number of blocks.
The argument is deliberately elementary; the hard part is producing
these hypotheses from the geometric scale decomposition. -/
theorem greedy_block_count_bound
    (blocks : ℕ) (α δ L M : ℝ)
    (hαδ : 0 < α - δ) (hM : 0 < M)
    (htotal : ((blocks : ℝ) - 1) * ((α - δ) * M ^ 2) < L * M ^ 2) :
    (blocks : ℝ) < 1 + L / (α - δ) := by
  have hsquare : 0 < M ^ 2 := sq_pos_of_pos hM
  have hweighted : (((blocks : ℝ) - 1) * (α - δ)) * M ^ 2 <
      L * M ^ 2 := by simpa only [mul_assoc] using htotal
  have hstep : ((blocks : ℝ) - 1) * (α - δ) < L :=
    (mul_lt_mul_right hsquare).mp hweighted
  have hquot : (blocks : ℝ) - 1 < L / (α - δ) :=
    (lt_div_iff₀ hαδ).2 hstep
  linarith

/-- If every nonlast block has mass `> (α/2)*M²` and total mass is
at most `L*M²`, the number of blocks is bounded by `1+2L/α`.
This is the simple numeric consequence used when `δ ≤ α/2`. -/
theorem half_density_block_count
    (blocks : ℕ) (α L M : ℝ)
    (hα : 0 < α) (hM : 0 < M)
    (hbudget : ((blocks : ℝ) - 1) * (α * M ^ 2 / 2) < L * M ^ 2) :
    (blocks : ℝ) < 1 + 2 * L / α := by
  have hαhalf : 0 < α / 2 := by positivity
  have hsquare : 0 < M ^ 2 := sq_pos_of_pos hM
  have hweighted : (((blocks : ℝ) - 1) * (α / 2)) * M ^ 2 <
      L * M ^ 2 := by
    convert hbudget using 1 <;> ring
  have hstep : ((blocks : ℝ) - 1) * (α / 2) < L :=
    (mul_lt_mul_right hsquare).mp hweighted
  have hquot : (blocks : ℝ) - 1 < L / (α / 2) :=
    (lt_div_iff₀ hαhalf).2 hstep
  have hEq : L / (α / 2) = 2 * L / α := by
    field_simp [ne_of_gt hα]
    <;> ring
  rw [hEq] at hquot
  linarith

end OpenAI086
