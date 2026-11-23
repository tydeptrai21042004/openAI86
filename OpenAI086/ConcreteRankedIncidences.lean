import Mathlib
import OpenAI086.RankedTwoAxisChain

/-!
# Lemma 8.5: concrete cardinal-fraction budgets from per-label data

The hypotheses below quantify directly over changing finite sets of
labels, with per-label occurrence counts. They deduce the two aggregate
exceptional-density budgets used in Lemma 8.6. To avoid pretending
that an enumeration has already been constructed, `hheightRank` and
`hpositionRank` explicitly request the first-entry rank condition.

A fixed ordering by `Fin M` is used in this staging theorem. The paper
allows different entry orders on the two axes; constructing those
orderings from arbitrary nested sets remains open in this repository.
-/

namespace OpenAI086

/-- The number of members in a finite set is the sum of its indicator
on the ambient finite label universe, including at zero cardinality. -/
theorem finite_label_card_fraction_as_sum {M : ℕ}
    (S E : Finset (Fin M)) :
    (((E ∩ S).card : ℝ) / (S.card : ℝ)) =
      ∑ r : Fin M,
        if r ∈ E ∩ S then (1 : ℝ) / (S.card : ℝ) else 0 := by
  classical
  simp [Finset.sum_ite, div_eq_mul_inv]

/-- Actual finite-set form of Lemma 8.5 with each label's index as its
entry rank: a per-label occurrence budget controls the *normalized*
exceptional-set cardinalities across an increasing collection. -/
theorem concrete_exceptional_fraction_from_rank
    {M T : ℕ} (S E : Fin T → Finset (Fin M)) (A : ℝ)
    (hsize : ∀ (t : Fin T) (r : Fin M), r ∈ E t ∩ S t →
      r.val + 1 ≤ (S t).card)
    (hinc : ∀ r : Fin M,
      (∑ t : Fin T,
        if r ∈ E t ∩ S t then (1 : ℝ) else 0) ≤ A) :
    (∑ t : Fin T,
      (((E t ∩ S t).card : ℝ) / ((S t).card : ℝ))) ≤
      A * finiteRankHarmonic M := by
  classical
  have h := ranked_exceptional_density_le T M A
    (fun t r => r ∈ E t ∩ S t) (fun t => (S t).card)
    hsize hinc
  calc
    (∑ t : Fin T,
      (((E t ∩ S t).card : ℝ) / ((S t).card : ℝ))) =
        ∑ t : Fin T, ∑ r : Fin M,
          if r ∈ E t ∩ S t then (1 : ℝ) / ((S t).card : ℝ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            exact finite_label_card_fraction_as_sum (S t) (E t)
    _ ≤ A * finiteRankHarmonic M := h

end OpenAI086
