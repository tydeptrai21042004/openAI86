import Mathlib

/-!
# Why the initial pair-incidence bound is insufficient for Lemma 9.1

A frequent error when attempting to formalize the sparse-counting result
is to infer a positive power of the density from the estimate that each
pair occurs at most `L` times. That is false without the additive
structure and tests used in the actual paper.

Our explicit construction indexes the scales by ordered pairs of labels
and places exactly one pair in each scale. Every pair occurs exactly
once, the density at each scale is `1/M²`, but the total pair mass is
`M²`. It is a formal obstruction to proving a power saving from just
the coarse mass hypotheses. It does NOT contradict Lemma 9.1, whose
hypotheses are substantially stronger.
-/

namespace OpenAI086

/-- Each scale, indexed by a pair of labels, contains exactly one pair. -/
theorem singleton_pair_at_every_scale (M : ℕ) (s : Fin M × Fin M) :
    (∑ a : Fin M, ∑ b : Fin M,
      if s = (a, b) then (1 : ℕ) else 0) = 1 := by
  classical
  rcases s with ⟨a, b⟩
  simp

/-- Each pair is selected at exactly one scale. -/
theorem singleton_pair_one_occurrence (M : ℕ) (a b : Fin M) :
    (∑ s : Fin M × Fin M,
      if s = (a, b) then (1 : ℕ) else 0) = 1 := by
  classical
  simp

/-- Despite arbitrarily small per-scale density, the combined mass is
exactly the total number of pairs. This pins down why the incidence
bound cannot by itself imply the paper's `δ^(1/2080)` gain. -/
theorem singleton_pair_total_mass (M : ℕ) :
    (∑ s : Fin M × Fin M, ∑ a : Fin M, ∑ b : Fin M,
      if s = (a, b) then (1 : ℕ) else 0) = M * M := by
  classical
  calc
    (∑ s : Fin M × Fin M, ∑ a : Fin M, ∑ b : Fin M,
        if s = (a, b) then (1 : ℕ) else 0) =
      ∑ _s : Fin M × Fin M, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro s _
        exact singleton_pair_at_every_scale M s
    _ = M * M := by simp [Fintype.card_prod]

end OpenAI086
