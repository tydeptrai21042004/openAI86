import Mathlib

/-!
# Lemma 8.5: canonical first-entry ordering for nested finite sets

For a finite label universe, construct each label's *actual first entry
position* from the nested sets, then order labels lexicographically by
(first-entry time, original label index). This removes the arbitrary
`r.val + 1 ≤ |S_t|` assumption at the level of the counting geometry.

The resulting rank is mathematically canonical and is injective.  This
module does not claim that the final harmonic summation of Lemma 8.5,
or any analytic assertion in Theorem 1.1, has been formalized.

Because the pinned Lean/Mathlib toolchain cannot currently run in this
workspace, these definitions and proof terms remain uncompiled candidates.
-/

namespace OpenAI086

/-- Minimal time when a label enters an increasing family. The coverage
assumption is used only to ensure the minimization is nonempty. -/
noncomputable def firstEntryTime {M : ℕ}
    (S : ℕ → Finset (Fin M))
    (hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S t)
    (r : Fin M) : ℕ :=
  Nat.find (hcover r)

/-- The first entry is an actual membership event. -/
theorem first_entry_mem {M : ℕ}
    (S : ℕ → Finset (Fin M))
    (hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S t)
    (r : Fin M) :
    r ∈ S (firstEntryTime S hcover r) := by
  unfold firstEntryTime
  exact Nat.find_spec (hcover r)

/-- Every later membership occurs after the label's first entry. -/
theorem first_entry_le_of_mem {M : ℕ}
    (S : ℕ → Finset (Fin M))
    (hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S t)
    (r : Fin M) (t : ℕ) (hr : r ∈ S t) :
    firstEntryTime S hcover r ≤ t := by
  unfold firstEntryTime
  exact Nat.find_min' (hcover r) hr

/-- Lexicographic weak order: chronological entry first, then the
original label index to break simultaneous-arrival ties. -/
def chronologicalLE {M : ℕ}
    (entry : Fin M → ℕ) (r s : Fin M) : Prop :=
  entry r < entry s ∨ (entry r = entry s ∧ r.val ≤ s.val)

/-- All labels preceding `r` in the entry-time order, including `r`.
Using a weak order is important for the rank to be at least one. -/
noncomputable def chronologicalPrefix {M : ℕ}
    (entry : Fin M → ℕ) (r : Fin M) : Finset (Fin M) :=
  Finset.univ.filter (fun s => chronologicalLE entry s r)

/-- Rank is the number of labels not later than the chosen label. -/
noncomputable def chronologicalRank {M : ℕ}
    (entry : Fin M → ℕ) (r : Fin M) : ℕ :=
  (chronologicalPrefix entry r).card

theorem chronological_prefix_mem_iff {M : ℕ}
    (entry : Fin M → ℕ) (r s : Fin M) :
    s ∈ chronologicalPrefix entry r ↔ chronologicalLE entry s r := by
  classical
  simp [chronologicalPrefix]

/-- Every chronological prefix contains its endpoint. -/
theorem chronological_rank_pos {M : ℕ}
    (entry : Fin M → ℕ) (r : Fin M) :
    0 < chronologicalRank entry r := by
  classical
  unfold chronologicalRank
  apply Finset.card_pos.mpr
  refine ⟨r, ?_⟩
  rw [chronological_prefix_mem_iff]
  exact Or.inr ⟨rfl, le_rfl⟩

/-- Its rank never exceeds the number of labels in the universe. -/
theorem chronological_rank_le_universe {M : ℕ}
    (entry : Fin M → ℕ) (r : Fin M) :
    chronologicalRank entry r ≤ M := by
  classical
  unfold chronologicalRank chronologicalPrefix
  have hsub :
      (Finset.univ.filter (fun s : Fin M => chronologicalLE entry s r)) ⊆
        (Finset.univ : Finset (Fin M)) := Finset.filter_subset _ _
  have h := Finset.card_le_card hsub
  simpa using h

/-- A chronologically earlier label must already belong to every
nested set containing the later label. In particular the corresponding
first-entry rank does not exceed the containing set's cardinality.
This is the actual missing size fact from Lemma 8.5, without fixing
any a priori rank permutation. -/
theorem chronological_prefix_subset_at_time {M : ℕ}
    (S : ℕ → Finset (Fin M))
    (hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S t)
    (hmono : Monotone S)
    (r : Fin M) (t : ℕ) (hrt : r ∈ S t) :
    chronologicalPrefix (firstEntryTime S hcover) r ⊆ S t := by
  classical
  intro s hs
  have hsle : firstEntryTime S hcover s ≤
      firstEntryTime S hcover r := by
    rw [chronological_prefix_mem_iff] at hs
    rcases hs with hlt | ⟨heq, _⟩
    · exact Nat.le_of_lt hlt
    · exact le_of_eq heq
  have hrt' := first_entry_le_of_mem S hcover r t hrt
  have hst : firstEntryTime S hcover s ≤ t := hsle.trans hrt'
  exact hmono hst (first_entry_mem S hcover s)

/-- The size/rank inequality required in the density proof, now
*derived* from any monotone label chain. -/
theorem chronological_rank_le_card_at_time {M : ℕ}
    (S : ℕ → Finset (Fin M))
    (hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S t)
    (hmono : Monotone S)
    (r : Fin M) (t : ℕ) (hrt : r ∈ S t) :
    chronologicalRank (firstEntryTime S hcover) r ≤ (S t).card := by
  unfold chronologicalRank
  exact Finset.card_le_card
    (chronological_prefix_subset_at_time S hcover hmono r t hrt)

/-- Strictly ordered keys have strictly ordered prefix cardinalities.
In particular equal first-entry times do not merge distinct labels. -/
theorem chronological_rank_lt_of_strict {M : ℕ}
    (entry : Fin M → ℕ) (r s : Fin M)
    (hrs : chronologicalLE entry r s)
    (hne : r ≠ s) :
    chronologicalRank entry r < chronologicalRank entry s := by
  classical
  have hval : r.val ≠ s.val := by
    intro h
    exact hne (Fin.ext h)
  have hnot : ¬ chronologicalLE entry s r := by
    unfold chronologicalLE at hrs ⊢
    omega
  have hsub : chronologicalPrefix entry r ⊆ chronologicalPrefix entry s := by
    intro z hz
    rw [chronological_prefix_mem_iff] at hz ⊢
    unfold chronologicalLE at hrs hz ⊢
    omega
  have hsmem : s ∈ chronologicalPrefix entry s := by
    rw [chronological_prefix_mem_iff]
    exact Or.inr ⟨rfl, le_rfl⟩
  have hsnot : s ∉ chronologicalPrefix entry r := by
    rw [chronological_prefix_mem_iff]
    exact hnot
  have hincl : insert s (chronologicalPrefix entry r) ⊆
      chronologicalPrefix entry s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzs | hz
    · simpa [hzs] using hsmem
    · exact hsub hz
  have hc := Finset.card_le_card hincl
  have he := Finset.card_insert_of_notMem hsnot
  unfold chronologicalRank
  omega

/-- The canonical chronological ranks are distinct, even if many
labels enter at exactly the same time. -/
theorem chronological_rank_injective {M : ℕ}
    (entry : Fin M → ℕ) : Function.Injective (chronologicalRank entry) := by
  intro r s heq
  by_contra hne
  have hdiff : r.val ≠ s.val := by
    intro h
    exact hne (Fin.ext h)
  have hchoice : chronologicalLE entry r s ∨
      chronologicalLE entry s r := by
    unfold chronologicalLE
    omega
  rcases hchoice with hrs | hsr
  · have hlt := chronological_rank_lt_of_strict entry r s hrs hne
    omega
  · have hlt := chronological_rank_lt_of_strict entry s r hsr (Ne.symm hne)
    omega

/-- The chronological rank, shifted down by one, is a genuine index
of the original finite universe. -/
noncomputable def chronologicalRankIndex {M : ℕ}
    (entry : Fin M → ℕ) (r : Fin M) : Fin M :=
  ⟨chronologicalRank entry r - 1, by
    have hp := chronological_rank_pos entry r
    have hb := chronological_rank_le_universe entry r
    omega⟩

/-- First-entry ordering constructs an injection of the finite label
universe into itself; no rank permutation is a hypothesis here. -/
theorem chronological_rank_index_injective {M : ℕ}
    (entry : Fin M → ℕ) :
    Function.Injective (chronologicalRankIndex entry) := by
  intro r s heq
  have hval : (chronologicalRankIndex entry r).val =
      (chronologicalRankIndex entry s).val := congrArg Fin.val heq
  have hp := chronological_rank_pos entry r
  have hq := chronological_rank_pos entry s
  have hrank : chronologicalRank entry r = chronologicalRank entry s := by
    change chronologicalRank entry r - 1 =
      chronologicalRank entry s - 1 at hval
    omega
  exact chronological_rank_injective entry hrank

end OpenAI086
