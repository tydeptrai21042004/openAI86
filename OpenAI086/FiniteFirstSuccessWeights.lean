import Mathlib
import OpenAI086.Packing

/-!
# First-success weights and finite failure histories (§9.1)

The manuscript selects the first successful sampled height. Before the
probabilistic estimates can be formalized, the finite geometric
accounting and the failure-history summation must be explicit.

These are genuine scalar identities, valid at any finite horizon. They
are *not* claims of independence or estimates for the paper's mode masks.
-/

namespace OpenAI086

/-- Exact finite accounting for first-success weights plus the
remaining no-success mass. The identity is algebraic for every `q`. -/
theorem finite_first_success_weight_identity (q : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 - q) * q ^ n) + q ^ N = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ n ∈ Finset.range (N + 1), (1 - q) * q ^ n) + q ^ (N + 1) =
            (∑ n ∈ Finset.range N, (1 - q) * q ^ n) + q ^ N := by
              rw [Finset.sum_range_succ, pow_succ]
              ring
        _ = 1 := ih

/-- For a failure probability between zero and one, the total mass of
successful finite histories is at most one. -/
theorem finite_first_success_weight_le_one
    (q : ℝ) (N : ℕ) (hq0 : 0 ≤ q) :
    (∑ n ∈ Finset.range N, (1 - q) * q ^ n) ≤ 1 := by
  have h := finite_first_success_weight_identity q N
  have hp : 0 ≤ q ^ N := pow_nonneg hq0 N
  linarith

/-- If the combined cost of first-failure role assignments is bounded
by `A*r^n`, with `r < 1`, the whole finite history is bounded without
any factor depending on the horizon `N`. -/
theorem finite_failure_history_geometric_budget
    (A r : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ n ∈ Finset.range N, A * r ^ n) ≤ A / (1 - r) := by
  calc
    (∑ n ∈ Finset.range N, A * r ^ n) =
        A * (∑ n ∈ Finset.range N, r ^ n) := by rw [Finset.mul_sum]
    _ ≤ A * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left (geometric_sum_uniform r hr0 hr1 N) hA
    _ = A / (1 - r) := by ring

end OpenAI086
