import Mathlib
import OpenAI086.EntryRankConcrete

/-!
# Lemma 8.5: produce entry-rank cardinality from concrete prefix sets

If primary labels have been assigned first-entry ranks 0,1,...,
then a set containing label r and every earlier rank has at least r+1
members. This small lemma removes the rank-size hypothesis in the
important initial-segment specialization of V10's exception bound.
For arbitrary evolving sets one must STILL construct a compatible
first-entry enumeration; that combinatorial construction is not claimed.
-/

namespace OpenAI086

/-- The first r+1 natural ranks are distinct members of the given set. -/
theorem finite_prefix_members_force_cardinality
    (S : Finset ℕ) (r : ℕ)
    (hprefix : ∀ k ≤ r, k ∈ S) :
    r + 1 ≤ S.card := by
  have hsub : Finset.range (r + 1) ⊆ S := by
    intro k hk
    apply hprefix k
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simpa using Finset.card_le_card hsub

/-- Entry-rank exceptional energy, when the containing sets already
use the chronological first-entry ordering of natural-number labels. -/
theorem prefix_entry_exceptional_density_le
    (T M : ℕ) (A : ℝ)
    (S : Fin T → Finset ℕ)
    (active : Fin T → Fin M → Prop)
    (hprefix : ∀ (t : Fin T) (r : Fin M), active t r →
      ∀ k ≤ r.val, k ∈ S t)
    (hinc : ∀ r : Fin M,
      (∑ t : Fin T, if active t r then (1 : ℝ) else 0) ≤ A) :
    (∑ t : Fin T, ∑ r : Fin M,
      if active t r then (1 : ℝ) / ((S t).card : ℝ) else 0) ≤
      A * (∑ r : Fin M, (1 : ℝ) / ((r.val + 1 : ℕ) : ℝ)) := by
  classical
  exact ranked_exceptional_density_le T M A active
    (fun t => (S t).card)
    (fun t r hr => finite_prefix_members_force_cardinality (S t) r.val
      (hprefix t r hr)) hinc

end OpenAI086
