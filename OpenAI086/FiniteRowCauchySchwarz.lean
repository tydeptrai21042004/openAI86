import Mathlib
import OpenAI086.CompressionRowError

/-!
# Lemma 3.4: removing the assumed finite Cauchy--Schwarz premise

The previous `CompressionRowError` established the row summation only after
Cauchy--Schwarz was passed in as a hypothesis for every row.  This file
proves the scalar finite Cauchy--Schwarz inequality independently using
the nonnegative squares `(aᵢ bⱼ - aⱼ bᵢ)^2` and then discharges that
hypothesis.  Its conclusion has no factor involving the number of rows
or labels.  Actual local operator Bessel hypotheses are still open.
-/

namespace OpenAI086

private theorem finite_pair_sum_product
    {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i : ι, f i) * (∑ j : ι, g j) =
      ∑ i : ι, ∑ j : ι, f i * g j := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- A finite real Cauchy--Schwarz inequality with an explicit elementary
proof. No Hilbert-space inequality is assumed. -/
theorem finite_row_cauchy_schwarz {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    (∑ i : ι, a i * b i) ^ 2 ≤
      (∑ i : ι, (a i) ^ 2) * (∑ i : ι, (b i) ^ 2) := by
  classical
  have hpoint (i j : ι) :
      2 * (a i * b i) * (a j * b j) ≤
        (a i) ^ 2 * (b j) ^ 2 + (a j) ^ 2 * (b i) ^ 2 := by
    nlinarith [sq_nonneg (a i * b j - a j * b i)]
  have hsum :
      (∑ i : ι, ∑ j : ι, 2 * (a i * b i) * (a j * b j)) ≤
        (∑ i : ι, ∑ j : ι,
          (a i) ^ 2 * (b j) ^ 2 + (a j) ^ 2 * (b i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hpoint i j
  have hleft :
      (∑ i : ι, ∑ j : ι, 2 * (a i * b i) * (a j * b j)) =
        2 * (∑ i : ι, a i * b i) ^ 2 := by
    calc
      (∑ i : ι, ∑ j : ι, 2 * (a i * b i) * (a j * b j)) =
          2 * (∑ i : ι, ∑ j : ι, (a i * b i) * (a j * b j)) := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = 2 * ((∑ i : ι, a i * b i) * (∑ j : ι, a j * b j)) := by
            rw [finite_pair_sum_product]
      _ = _ := by ring
  have hswap :
      (∑ i : ι, ∑ j : ι, (a j) ^ 2 * (b i) ^ 2) =
        (∑ i : ι, ∑ j : ι, (a i) ^ 2 * (b j) ^ 2) := by
    rw [Finset.sum_comm]
  have hright :
      (∑ i : ι, ∑ j : ι,
        (a i) ^ 2 * (b j) ^ 2 + (a j) ^ 2 * (b i) ^ 2) =
          2 * ((∑ i : ι, (a i) ^ 2) * (∑ i : ι, (b i) ^ 2)) := by
    calc
      (∑ i : ι, ∑ j : ι,
        (a i) ^ 2 * (b j) ^ 2 + (a j) ^ 2 * (b i) ^ 2) =
          (∑ i : ι, ∑ j : ι, (a i) ^ 2 * (b j) ^ 2) +
          (∑ i : ι, ∑ j : ι, (a j) ^ 2 * (b i) ^ 2) := by
            simp only [Finset.sum_add_distrib]
      _ = 2 * ((∑ i : ι, (a i) ^ 2) * (∑ i : ι, (b i) ^ 2)) := by
            rw [hswap]
            simp only [← finite_pair_sum_product]
            ring
  rw [hleft, hright] at hsum
  nlinarith

/-- The finite coefficient-error/Bessel estimate without taking
Cauchy--Schwarz as an external hypothesis. This is a strict improvement
of the finite row argument underlying Lemma 3.4, not its full operator
compression theorem. -/
theorem compression_row_error_from_bessel
    {Row Label : Type*} [Fintype Row] [Fintype Label]
    (err signal : Row → Label → ℝ) (energy : Label → ℝ) (τ : ℝ)
    (hsmall : ∀ r : Row,
      (∑ v : Label, (err r v) ^ 2) ≤ τ ^ 2)
    (hbessel : ∀ v : Label,
      (∑ r : Row, (signal r v) ^ 2) ≤ energy v) :
    (∑ r : Row, (∑ v : Label, err r v * signal r v) ^ 2) ≤
      τ ^ 2 * (∑ v : Label, energy v) := by
  classical
  apply compression_coefficient_error_budget err signal energy τ hsmall
  · intro r
    exact finite_row_cauchy_schwarz (err r) (signal r)
  · exact hbessel

end OpenAI086
