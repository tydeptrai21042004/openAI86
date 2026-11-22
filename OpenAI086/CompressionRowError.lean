import Mathlib

/-!
# Lemma 3.4: finite row error after coefficient stopping

On pp. 12--13, coefficient errors from moving from a cell to its
last anchor are controlled by (i) small squared coefficient energy,
(ii) Cauchy--Schwarz per row, (iii) Bessel bounds per label, and
(iv) the path-label squared-energy budget.

Here we formalize the exact **double-sum argument** after the standard
finite Cauchy--Schwarz and Bessel premises have been made explicit.
It is valid for arbitrarily many rows and labels and retains a sharp
`τ²` coefficient (no factor involving the number of labels).

The construction of the actual operators and the assumptions themselves
are still separate proof obligations, so this is not full Lemma 3.4.
-/

namespace OpenAI086

/-- An abstract real row model for the coefficient-error summation.
The hypotheses are finite Cauchy--Schwarz in each row and Bessel on
each fixed label. The conclusion has no row/label cardinality loss. -/
theorem compression_coefficient_error_budget
    {Row Label : Type*} [Fintype Row] [Fintype Label]
    (err signal : Row → Label → ℝ) (energy : Label → ℝ) (τ : ℝ)
    (hsmall : ∀ r : Row,
      (∑ v : Label, (err r v) ^ 2) ≤ τ ^ 2)
    (hcs : ∀ r : Row,
      (∑ v : Label, err r v * signal r v) ^ 2 ≤
      (∑ v : Label, (err r v) ^ 2) *
      (∑ v : Label, (signal r v) ^ 2))
    (hbessel : ∀ v : Label,
      (∑ r : Row, (signal r v) ^ 2) ≤ energy v) :
    (∑ r : Row, (∑ v : Label, err r v * signal r v) ^ 2) ≤
      τ ^ 2 * (∑ v : Label, energy v) := by
  classical
  have ht : 0 ≤ τ ^ 2 := sq_nonneg τ
  calc
    (∑ r : Row, (∑ v : Label, err r v * signal r v) ^ 2) ≤
        ∑ r : Row, τ ^ 2 * (∑ v : Label, (signal r v) ^ 2) := by
          apply Finset.sum_le_sum
          intro r _
          have hn : 0 ≤ ∑ v : Label, (signal r v) ^ 2 :=
            Finset.sum_nonneg (fun v _ => sq_nonneg (signal r v))
          exact (hcs r).trans
            (mul_le_mul_of_nonneg_right (hsmall r) hn)
    _ = τ ^ 2 * (∑ r : Row, ∑ v : Label, (signal r v) ^ 2) := by
          rw [Finset.mul_sum]
    _ = τ ^ 2 * (∑ v : Label, ∑ r : Row, (signal r v) ^ 2) := by
          rw [Finset.sum_comm]
    _ ≤ τ ^ 2 * (∑ v : Label, energy v) := by
          apply mul_le_mul_of_nonneg_left _ ht
          apply Finset.sum_le_sum
          intro v _
          exact hbessel v

end OpenAI086
