import Mathlib
import OpenAI086.FiniteBadHeightSet

/-!
# Lemma 8.6: the original UNION-based bad-height test

The PDF uses the exceptional fraction |(X ∪ Y) ∩ C| / |C|, rather
than an abstract numerical predicate or the sum of two independently
postulated exceptional fractions.  The results below bridge exactly
that union-based predicate to the pointwise upper bound used in V10.

The cardinality rank is kept as an arbitrary monotone natural-valued
binning, so the same arguments apply to floor-log cardinality bins.
No bound on exceptional incidences is assumed or proved in this file.
-/

namespace OpenAI086

/-- The union of two exceptional subsets contributes at most the sum
of their individual intersections with the containing set. -/
theorem finite_exceptional_union_card_le
    {α : Type*} [DecidableEq α] (X Y C : Finset α) :
    ((X ∪ Y) ∩ C).card ≤ (X ∩ C).card + (Y ∩ C).card := by
  have hsub : (X ∪ Y) ∩ C ⊆ (X ∩ C) ∪ (Y ∩ C) := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hxy, hc⟩
    rcases Finset.mem_union.mp hxy with hx | hy
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hc⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hy, hc⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The precise union density in Lemma 8.6 is controlled by its two
separate nonnegative densities.  No division-by-zero assumption is
needed for this inequality. -/
theorem finite_exceptional_union_fraction_le
    {α : Type*} [DecidableEq α] (X Y C : Finset α) :
    (((X ∪ Y) ∩ C).card : ℝ) / (C.card : ℝ) ≤
      ((X ∩ C).card : ℝ) / (C.card : ℝ) +
      ((Y ∩ C).card : ℝ) / (C.card : ℝ) := by
  have hc : (((X ∪ Y) ∩ C).card : ℝ) ≤
      ((X ∩ C).card : ℝ) + ((Y ∩ C).card : ℝ) := by
    exact_mod_cast finite_exceptional_union_card_le X Y C
  calc
    (((X ∪ Y) ∩ C).card : ℝ) / (C.card : ℝ) ≤
        (((X ∩ C).card : ℝ) + ((Y ∩ C).card : ℝ)) /
          (C.card : ℝ) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = _ := by rw [add_div]

/-- A faithful (post-lag) finite-set formulation of the PDF's test.
In particular, the alternative is the UNION fraction, not the sum of
fractions. The latter appears only in an upper estimate. -/
noncomputable def paperUnionBadHeight
    {α : Type*} [DecidableEq α]
    (rank : ℕ → ℕ) (Pold C X Y : Finset α) (beta : ℝ) : ℝ := by
  classical
  exact if rank Pold.card ≠ rank C.card ∨
      beta < (((X ∪ Y) ∩ C).card : ℝ) / (C.card : ℝ)
    then 1 else 0

/-- Unlike V10's predicate bridge, this starts from the *actual*
union of exceptional labels used by the manuscript. -/
theorem paper_union_bad_height_pointwise
    {α : Type*} [DecidableEq α]
    (rank : ℕ → ℕ) (hrank : Monotone rank)
    (Pold Pnew C X Y : Finset α)
    (hOld : Pold ⊆ Pnew) (hNew : Pnew ⊆ C)
    (beta : ℝ) (hbeta : 0 < beta) :
    paperUnionBadHeight rank Pold C X Y beta ≤
      ((rank Pnew.card : ℝ) - (rank Pold.card : ℝ)) +
      ((rank C.card : ℝ) - (rank Pnew.card : ℝ)) +
      (((X ∩ C).card : ℝ) / (C.card : ℝ) +
       ((Y ∩ C).card : ℝ) / (C.card : ℝ)) / beta := by
  classical
  let u : ℝ := ((X ∩ C).card : ℝ) / (C.card : ℝ)
  let v : ℝ := ((Y ∩ C).card : ℝ) / (C.card : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hfrac :
      (((X ∪ Y) ∩ C).card : ℝ) / (C.card : ℝ) ≤ u + v := by
    exact finite_exceptional_union_fraction_le X Y C
  have himp :
      (rank Pold.card ≠ rank C.card ∨
        beta < (((X ∪ Y) ∩ C).card : ℝ) / (C.card : ℝ)) →
      (rank Pold.card ≠ rank C.card ∨ beta < u + v) := by
    intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (lt_of_lt_of_le h hfrac)
  have htest :
      paperUnionBadHeight rank Pold C X Y beta ≤
      (if rank Pold.card ≠ rank C.card ∨ beta < u + v
       then (1 : ℝ) else 0) := by
    unfold paperUnionBadHeight
    by_cases h : rank Pold.card ≠ rank C.card ∨
        beta < (((X ∪ Y) ∩ C).card : ℝ) / (C.card : ℝ)
    · have ht := himp h
      simp [h, ht]
    · simp only [if_neg h]
      split_ifs <;> norm_num
  have hbound := finite_bad_height_from_nested_sets rank hrank
    Pold Pnew C hOld hNew u v beta hu hv hbeta
  exact htest.trans hbound

end OpenAI086
