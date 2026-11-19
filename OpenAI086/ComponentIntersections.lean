import Mathlib

/-!
# OpenAI #086, Lemma 8.10: intersections of large predecessor components

These are actual finite-set inequalities needed in the hereditary
representative argument on paper pp. 74--75. The graph-persistence and
representative-selection parts of Lemma 8.10 are **not** proved here.

Unlike a model with unrelated cardinality variables, these results apply
to genuine finite subsets of one ambient set and explicitly retain the
subset hypotheses from the manuscript.
-/

namespace OpenAI086

/-- Inclusion-exclusion with an ambient set: if `A,B ⊆ F`, their overlap
has at least the amount by which their sizes exceed the size of `F`. -/
theorem ambient_component_intersection_bound
    {α : Type*} [DecidableEq α] (F A B : Finset α)
    (hA : A ⊆ F) (hB : B ⊆ F) :
    A.card + B.card ≤ F.card + (A ∩ B).card := by
  have hUnion : (A ∪ B).card ≤ F.card :=
    Finset.card_le_card (Finset.union_subset hA hB)
  have hIdentity := Finset.card_union_add_card_inter A B
  omega

/-- Two strict majorities inside a common finite ambient set intersect.
This is used again in the consistency argument for inherited labels. -/
theorem strict_majorities_intersect
    {α : Type*} [DecidableEq α] (F A B : Finset α)
    (hA : A ⊆ F) (hB : B ⊆ F)
    (hAsize : F.card < 2 * A.card)
    (hBsize : F.card < 2 * B.card) :
    (A ∩ B).Nonempty := by
  have hbound := ambient_component_intersection_bound F A B hA hB
  have hpos : 0 < (A ∩ B).card := by omega
  exact Finset.card_pos.mp hpos

/-- The specific `1.1` and `1.1²` comparison from Lemma 8.10.  Here
`11|A| > 10|F|` and `121|B| > 100|F|` express the strict lower bounds.
The paper only needs a `> |F|/10` intersection; the stated estimate is
exactly that integer inequality, avoiding floating-point rounding. -/
theorem quantitative_predecessor_overlap
    {α : Type*} [DecidableEq α] (F A B : Finset α)
    (hA : A ⊆ F) (hB : B ⊆ F)
    (hAsize : 10 * F.card < 11 * A.card)
    (hBsize : 100 * F.card < 121 * B.card) :
    F.card < 10 * (A ∩ B).card := by
  have hbound := ambient_component_intersection_bound F A B hA hB
  omega

/-- Quantitative overlap guarantees a shared primary if the ambient
component is nonempty. -/
theorem predecessor_overlap_nonempty
    {α : Type*} [DecidableEq α] (F A B : Finset α)
    (hF : F.Nonempty)
    (hA : A ⊆ F) (hB : B ⊆ F)
    (hAsize : 10 * F.card < 11 * A.card)
    (hBsize : 100 * F.card < 121 * B.card) :
    (A ∩ B).Nonempty := by
  have hlower := quantitative_predecessor_overlap F A B hA hB hAsize hBsize
  have hpos : 0 < (A ∩ B).card := by
    have hcard : 0 < F.card := Finset.card_pos.mpr hF
    omega
  exact Finset.card_pos.mp hpos

end OpenAI086
