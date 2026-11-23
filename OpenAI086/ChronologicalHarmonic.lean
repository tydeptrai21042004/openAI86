import Mathlib
import OpenAI086.ChronologicalIncidence
import OpenAI086.RankedTwoAxisChain

/-!
# Lemma 8.5: canonical first-entry ranks have harmonic cost H_M

A distinct positive rank in {1,...,M} is automatically a permutation
of those ranks. Reindex the finite sum with that permutation to finish
the harmonic incidence estimate for actual nested finite sets.

The label universe is assumed to consist of labels that appear by some
finite time. This is the intended convention when using M = |union S_t|.
This is an independent, uncompiled Lean proof candidate; no `sorry`,
`admit`, auxiliary analytic hypotheses, or upstream theorem is used.
-/

namespace OpenAI086

/-- The rank-index map is a permutation, not an additional hypothesis. -/
noncomputable def chronologicalRankEquiv {M : ℕ}
    (entry : Fin M → ℕ) : Fin M ≃ Fin M :=
  Equiv.ofBijective (chronologicalRankIndex entry)
    (Finite.injective_iff_bijective.mp
      (chronological_rank_index_injective entry))

/-- Restoring the one-based index after subtracting one. -/
theorem chronological_rank_index_val_succ {M : ℕ}
    (entry : Fin M → ℕ) (r : Fin M) :
    (chronologicalRankIndex entry r).val + 1 = chronologicalRank entry r := by
  change chronologicalRank entry r - 1 + 1 = chronologicalRank entry r
  have hp := chronological_rank_pos entry r
  omega

/-- The sum of reciprocal chronological ranks is exactly the ordinary
harmonic sum. The tie-breaking index ensures there is no rank collision. -/
theorem chronological_rank_harmonic {M : ℕ}
    (entry : Fin M → ℕ) :
    (∑ r : Fin M, (1 : ℝ) / (chronologicalRank entry r : ℝ)) =
      finiteRankHarmonic M := by
  classical
  let e : Fin M ≃ Fin M := chronologicalRankEquiv entry
  have hindex (r : Fin M) :
      (e r).val + 1 = chronologicalRank entry r := by
    simpa [e, chronologicalRankEquiv] using
      (chronological_rank_index_val_succ entry r)
  calc
    (∑ r : Fin M, (1 : ℝ) / (chronologicalRank entry r : ℝ)) =
      ∑ r : Fin M, (1 : ℝ) / (((e r).val + 1 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hindex r]
    _ = ∑ k : Fin M, (1 : ℝ) / (((k.val + 1 : ℕ) : ℝ)) :=
      Equiv.sum_comp e (fun k : Fin M =>
        (1 : ℝ) / (((k.val + 1 : ℕ) : ℝ)))
    _ = finiteRankHarmonic M := rfl

/-- Harmonic exceptional-density bound for *arbitrary* monotone
families of finite label sets, no first-entry rank-size assumptions.

For each label r, the number of times it lies in E_t intersection S_t
is bounded by A. Then the total normalized exception fraction is at
most A times H_M, with no assumption on how the labels were originally
numbered. This closes the finite combinatorial first-entry counting
step of Lemma 8.5 (not the entirety of Lemma 8.6). -/
theorem chronological_exception_fraction_harmonic
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
      A * finiteRankHarmonic M := by
  calc
    (∑ t : Fin T,
        (((E t ∩ S t.val).card : ℝ) / ((S t.val).card : ℝ))) ≤
      A * (∑ r : Fin M,
        (1 : ℝ) / (chronologicalRank (firstEntryTime S hcover) r : ℝ)) :=
        chronological_exception_fraction_bound S E hcover hmono A hinc
    _ = A * finiteRankHarmonic M := by
      rw [chronological_rank_harmonic]

end OpenAI086
