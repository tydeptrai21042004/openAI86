import Mathlib

/-!
# OpenAI #086, Lemma 9.1: pair-incidence mass bound

Formalizes the exact global mass estimate `sum_s N_s <= L M^2` used
before the greedy blocking step of the sparse-count proof (paper p. 83).
It uses the hypothesis that any ordered pair occurs in at most `L`
scale tests, with no restriction on the number of scales.

The strong `δ^(1/2080)` conclusion of Lemma 9.1 is still OPEN.
-/

namespace OpenAI086

/-- Finite double-counting, with an arbitrary number of scales and
arbitrary nonnegative natural-number incidence multiplicities. -/
theorem finite_incidence_mass_bound
    {σ α : Type*} [Fintype σ] [Fintype α]
    (occ : σ → α → ℕ) (L : ℕ)
    (hper : ∀ x : α, (∑ s : σ, occ s x) ≤ L) :
    (∑ s : σ, ∑ x : α, occ s x) ≤ L * Fintype.card α := by
  calc
    (∑ s : σ, ∑ x : α, occ s x) =
        ∑ x : α, ∑ s : σ, occ s x := by rw [Finset.sum_comm]
    _ ≤ ∑ _x : α, L := by
      apply Finset.sum_le_sum
      intro x _
      exact hper x
    _ = L * Fintype.card α := by simp [mul_comm]

/-- A pair test for `M` labels in two distinct roles occurs in at most
`L` scales: all such pair incidences together have mass at most `L*M²`.
This is the counting bound actually used at the start of Lemma 9.1. -/
theorem ordered_pair_occurrences_le
    (S M L : ℕ) (selected : Fin S → Fin M → Fin M → Prop)
    (hper : ∀ a b : Fin M,
       (∑ s : Fin S, if selected s a b then (1 : ℕ) else 0) ≤ L) :
    (∑ s : Fin S, ∑ a : Fin M, ∑ b : Fin M,
       if selected s a b then (1 : ℕ) else 0) ≤ L * M * M := by
  classical
  calc
    (∑ s : Fin S, ∑ a : Fin M, ∑ b : Fin M,
       if selected s a b then (1 : ℕ) else 0) =
        ∑ a : Fin M, ∑ b : Fin M, ∑ s : Fin S,
          if selected s a b then (1 : ℕ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
    _ ≤ ∑ _a : Fin M, ∑ _b : Fin M, L := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        exact hper a b
    _ = L * M * M := by
        simp [mul_assoc, mul_comm, mul_left_comm]

/-- After discarding any set of scales, the same pair mass budget still
holds. This is the initial reduction to `N_s ≤ δ M²` in paper p. 83. -/
theorem retained_pair_occurrences_le
    (S M L : ℕ) (retained : Finset (Fin S))
    (selected : Fin S → Fin M → Fin M → Prop)
    (hper : ∀ a b : Fin M,
       (∑ s : Fin S, if selected s a b then (1 : ℕ) else 0) ≤ L) :
    (∑ s ∈ retained, ∑ a : Fin M, ∑ b : Fin M,
       if selected s a b then (1 : ℕ) else 0) ≤ L * M * M := by
  classical
  have hfull := ordered_pair_occurrences_le S M L selected hper
  have hmono :
      (∑ s ∈ retained, ∑ a : Fin M, ∑ b : Fin M,
         if selected s a b then (1 : ℕ) else 0) ≤
      (∑ s : Fin S, ∑ a : Fin M, ∑ b : Fin M,
         if selected s a b then (1 : ℕ) else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ retained
    · intro s _ _
      exact Nat.zero_le _
  exact hmono.trans hfull

end OpenAI086
