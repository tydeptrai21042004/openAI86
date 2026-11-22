import Mathlib

/-!
# Finite pathwise packing (Section 3.1)

The manuscript passes from a pointwise budget along every spatial path
  `∑_{I∋y} a_I ≤ A`
to a length-weighted sum over cells by Tonelli.

This module proves the corresponding **finite weighted Fubini inequality**
with arbitrary nonnegative point masses. It does not claim the measurable
Tonelli theorem or the dyadic stopping construction from the paper.
The source and proof are independent and use only Mathlib.
-/

namespace OpenAI086

/-- Weighted finite Tonelli: summing a pathwise upper budget over points
bounds the total mass of all cell-point incidences.  This is uniform in
the number of cells and does not require any cell-disjointness. -/
theorem finite_weighted_path_budget
    {Point Cell : Type*} [Fintype Point] [Fintype Cell]
    (w : Point → ℝ) (occupancy : Cell → Point → ℝ) (A : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hpath : ∀ x, (∑ I : Cell, occupancy I x) ≤ A) :
    (∑ I : Cell, ∑ x : Point, w x * occupancy I x) ≤
      A * (∑ x : Point, w x) := by
  classical
  calc
    (∑ I : Cell, ∑ x : Point, w x * occupancy I x) =
        ∑ x : Point, ∑ I : Cell, w x * occupancy I x := by
          rw [Finset.sum_comm]
    _ = ∑ x : Point, w x * (∑ I : Cell, occupancy I x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ ≤ ∑ x : Point, w x * A := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left (hpath x) (hw x)
    _ = A * (∑ x : Point, w x) := by
          rw [← Finset.sum_mul]
          ring

/-- For nonnegative path budgets, the pointwise version also gives an
upper bound for each individual (nonnegative) point-weighted row. -/
theorem finite_single_cell_from_path_budget
    {Point Cell : Type*} [Fintype Point] [Fintype Cell]
    [DecidableEq Cell]
    (w : Point → ℝ) (occupancy : Cell → Point → ℝ) (A : ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hnonneg : ∀ I x, 0 ≤ occupancy I x)
    (hpath : ∀ x, (∑ I : Cell, occupancy I x) ≤ A)
    (J : Cell) :
    (∑ x : Point, w x * occupancy J x) ≤
      A * (∑ x : Point, w x) := by
  have hsingle (x : Point) : occupancy J x ≤ ∑ I : Cell, occupancy I x := by
    exact Finset.single_le_sum (fun I _ hne => hnonneg I x) (Finset.mem_univ J)
  calc
    (∑ x : Point, w x * occupancy J x) ≤
        ∑ x : Point, w x * (∑ I : Cell, occupancy I x) := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left (hsingle x) (hw x)
    _ ≤ ∑ x : Point, w x * A := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left (hpath x) (hw x)
    _ = A * (∑ x : Point, w x) := by
          rw [← Finset.sum_mul]
          ring

end OpenAI086
