import Mathlib
import OpenAI086.BadDensityThreshold

/-!
# Lemma 8.6: from nested finite label sets to the bad-height indicator

The first bad-height predicate on page 70 compares floor-log counts of
`P_(i,h-lag)` and `C_(i,h)`.  This file shows that the comparison is
controlled by TWO nonnegative gaps, corresponding exactly to the height
and position summands in the V10 telescoping bridge.

Instead of hard-coding base 1.1, we work with an arbitrary monotone
integer-valued rank function on cardinalities. The actual floor-log
binning is an instance of that hypothesis. The two exceptional fractions
are passed in nonnegative form; their rank-incidence control is proved
separately in RankedTwoAxisChain.
-/

namespace OpenAI086

/-- An elementary inclusion-to-rank bridge.  It is the crucial step
allowing a proof in terms of actual `Finset` label lists, rather than
postulating inequalities between their logarithmic cardinality ranks. -/
theorem finite_set_rank_monotone
    {α : Type*} [DecidableEq α]
    (rank : ℕ → ℕ) (hrank : Monotone rank)
    (P C : Finset α) (hPC : P ⊆ C) :
    rank P.card ≤ rank C.card :=
  hrank (Finset.card_le_card hPC)

/-- A nested triplet `Pold ⊆ Pnew ⊆ C` yields the exact numerical
pointwise upper bound for the bad-height indicator, including its
exceptional-density alternative.  No analytic hypotheses are needed.

The inequality is valid for ANY monotone integer binning of cardinality;
for the paper it is the floor of log_(1.1) of cardinality. -/
theorem finite_bad_height_from_nested_sets
    {α : Type*} [DecidableEq α]
    (rank : ℕ → ℕ) (hrank : Monotone rank)
    (Pold Pnew C : Finset α)
    (hOld : Pold ⊆ Pnew) (hNew : Pnew ⊆ C)
    (u v beta : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbeta : 0 < beta) :
    (if rank Pold.card ≠ rank C.card ∨ beta < u + v
      then (1 : ℝ) else 0) ≤
      ((rank Pnew.card : ℝ) - (rank Pold.card : ℝ)) +
      ((rank C.card : ℝ) - (rank Pnew.card : ℝ)) +
      (u + v) / beta := by
  have hfirst : rank Pold.card ≤ rank Pnew.card :=
    finite_set_rank_monotone rank hrank Pold Pnew hOld
  have hsecond : rank Pnew.card ≤ rank C.card :=
    finite_set_rank_monotone rank hrank Pnew C hNew
  have htest :
      (rank Pold.card ≠ rank C.card) ↔
        0 < (rank Pnew.card - rank Pold.card) +
          (rank C.card - rank Pnew.card) := by
    omega
  have hA :
      ((rank Pnew.card - rank Pold.card : ℕ) : ℝ) =
        (rank Pnew.card : ℝ) - (rank Pold.card : ℝ) :=
    Nat.cast_sub hfirst
  have hB :
      ((rank C.card - rank Pnew.card : ℕ) : ℝ) =
        (rank C.card : ℝ) - (rank Pnew.card : ℝ) :=
    Nat.cast_sub hsecond
  have hbound := integer_gap_or_density_bound
    (rank Pnew.card - rank Pold.card)
    (rank C.card - rank Pnew.card) u v beta hu hv hbeta
  simpa only [← htest, hA, hB] using hbound

end OpenAI086
