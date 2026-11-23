import Mathlib
import OpenAI086.ChronologicalFirstEntry
import OpenAI086.ConcreteRankedIncidences

/-!
# Lemma 8.5: exceptional density with the rank constructed from the sets

Unlike the V12 theorem `concrete_exceptional_fraction_from_rank`, this
bound does not assume that the label's ORIGINAL index is an entry rank.
It constructs first-entry times from the increasing list and proves the
needed denominator bound in `ChronologicalFirstEntry`.

The current conclusion keeps the exact sum over the constructed ranks.
To replace this by the usual `H_M` bound (as in the manuscript), one
needs to reindex these distinct ranks into `1,...,M`. The rank
injectivity theorem in the preceding module supplies that ingredient;
the final reindexing is deliberately not claimed here.
-/

namespace OpenAI086

/-- A normalized exceptional fraction bound for arbitrary nested finite
sets, with no assumed labeling by chronological entry order.

`hcover` only fixes the ambient finite set of labels. In applications
one may choose this universe to be the labels ever appearing in the
chain; all unused labels should be removed before applying the bound.
The per-label occurrence bound `A` is the only incidence hypothesis. -/
theorem chronological_exception_fraction_bound
    {M T : ℕ}
    (S : ℕ → Finset (Fin M))
    (E : Fin T → Finset (Fin M))
    (hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S t)
    (hmono : Monotone S)
    (A : ℝ)
    (hinc : ∀ r : Fin M,
      (∑ t : Fin T,
        if r ∈ E t ∩ S t.val then (1 : ℝ) else 0) ≤ A) :
    (∑ t : Fin T,
      (((E t ∩ S t.val).card : ℝ) / ((S t.val).card : ℝ))) ≤
      A * (∑ r : Fin M,
        (1 : ℝ) / ((chronologicalRank (firstEntryTime S hcover) r : ℕ) : ℝ)) := by
  classical
  let rank : Fin M → ℕ := chronologicalRank (firstEntryTime S hcover)
  have hper (r : Fin M) :
      (∑ t : Fin T,
        if r ∈ E t ∩ S t.val then
          (1 : ℝ) / ((S t.val).card : ℝ) else 0) ≤
      A * ((1 : ℝ) / (rank r : ℝ)) := by
    have hterm (t : Fin T) :
        (if r ∈ E t ∩ S t.val then
          (1 : ℝ) / ((S t.val).card : ℝ) else 0) ≤
        (if r ∈ E t ∩ S t.val then (1 : ℝ) else 0) *
          ((1 : ℝ) / (rank r : ℝ)) := by
      by_cases hr : r ∈ E t ∩ S t.val
      · simp only [if_pos hr, one_mul]
        have hpos : (0 : ℝ) < (rank r : ℝ) := by
          exact_mod_cast chronological_rank_pos
            (firstEntryTime S hcover) r
        have hsize : (rank r : ℝ) ≤ ((S t.val).card : ℝ) := by
          exact_mod_cast chronological_rank_le_card_at_time
            S hcover hmono r t.val (Finset.mem_inter.mp hr).2
        exact one_div_le_one_div_of_le hpos hsize
      · simp [hr]
    calc
      (∑ t : Fin T,
          if r ∈ E t ∩ S t.val then
            (1 : ℝ) / ((S t.val).card : ℝ) else 0) ≤
        ∑ t : Fin T,
          (if r ∈ E t ∩ S t.val then (1 : ℝ) else 0) *
            ((1 : ℝ) / (rank r : ℝ)) := by
              apply Finset.sum_le_sum
              intro t _
              exact hterm t
      _ = (∑ t : Fin T,
          if r ∈ E t ∩ S t.val then (1 : ℝ) else 0) *
            ((1 : ℝ) / (rank r : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ A * ((1 : ℝ) / (rank r : ℝ)) :=
          mul_le_mul_of_nonneg_right (hinc r) (by positivity)
  calc
    (∑ t : Fin T,
        (((E t ∩ S t.val).card : ℝ) / ((S t.val).card : ℝ))) =
      ∑ t : Fin T, ∑ r : Fin M,
        if r ∈ E t ∩ S t.val then
          (1 : ℝ) / ((S t.val).card : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        exact finite_label_card_fraction_as_sum (S t.val) (E t)
    _ = ∑ r : Fin M, ∑ t : Fin T,
          if r ∈ E t ∩ S t.val then
            (1 : ℝ) / ((S t.val).card : ℝ) else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ r : Fin M, A * ((1 : ℝ) / (rank r : ℝ)) := by
          apply Finset.sum_le_sum
          intro r _
          exact hper r
    _ = A * (∑ r : Fin M, (1 : ℝ) / (rank r : ℝ)) := by
          rw [Finset.mul_sum]

end OpenAI086
