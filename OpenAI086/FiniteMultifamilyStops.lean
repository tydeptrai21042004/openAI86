import Mathlib

/-!
# Arbitrarily many simultaneous stopping families

The proof of Lemma 3.1 and the outer reduction repeatedly combine
exceptional families, then restart on maximal disjoint stopped cells.
This file proves the exact **finite cardinality union estimate** for any
number of families, generalizing the previously checked four-set case.
The measurable stopping-time construction remains open.
-/

namespace OpenAI086

/-- A finite union cannot have more elements than the sum of the
individual cardinalities; overlap is explicitly permitted. -/
theorem finite_biUnion_card_le_sum
    {Index Point : Type*} [DecidableEq Point]
    (s : Finset Index) (S : Index → Finset Point) :
    (s.biUnion S).card ≤ ∑ i ∈ s, (S i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i rest hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      calc
        (S i ∪ rest.biUnion S).card ≤ (S i).card + (rest.biUnion S).card :=
          Finset.card_union_le _ _
        _ ≤ (S i).card + ∑ j ∈ rest, (S j).card :=
          Nat.add_le_add_left ih _

/-- With `K` as the common divisor of the per-family budget, the
entire stopped union has cost bounded by the *number* of families.
No fixed number of families is hardcoded in the conclusion. -/
theorem finite_multifamily_stopping_budget
    {Index Point : Type*} [DecidableEq Point]
    (s : Finset Index) (S : Index → Finset Point)
    (root : Finset Point) (K : ℕ)
    (hper : ∀ i ∈ s, K * (S i).card ≤ root.card) :
    K * (s.biUnion S).card ≤ s.card * root.card := by
  classical
  calc
    K * (s.biUnion S).card ≤ K * (∑ i ∈ s, (S i).card) :=
      Nat.mul_le_mul_left K (finite_biUnion_card_le_sum s S)
    _ = ∑ i ∈ s, K * (S i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ s, root.card := by
      apply Finset.sum_le_sum
      intro i hi
      exact hper i hi
    _ = s.card * root.card := by simp

end OpenAI086
