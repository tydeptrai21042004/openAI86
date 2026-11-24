import Mathlib
import OpenAI086.PaperStoppingPartition
import OpenAI086.PaperTopCount

/-! First tops, with the original depth and cell label. There is no
first top on a path without any successful use. -/
namespace OpenAI086

def v23IsFirstTop {Ω C : Type*} (cell : ℕ → Ω → C)
    (used : ℕ → C → Prop) (x : Ω) (n : ℕ) : Prop :=
  used n (cell n x) ∧ ∀ j < n, ¬ used j (cell j x)

theorem v23_first_top_exists {Ω C : Type*} (cell : ℕ → Ω → C)
    (used : ℕ → C → Prop) (x : Ω) (n : ℕ) (hn : used n (cell n x)) :
    ∃ t ≤ n, v23IsFirstTop cell used x t := by
  classical
  have h : ∃ t, used t (cell t x) := ⟨n, hn⟩
  refine ⟨Nat.find h, Nat.find_min' h hn, Nat.find_spec h, ?_⟩
  intro j hj huse
  have := Nat.find_min' h huse
  omega

theorem v23_first_top_unique {Ω C : Type*} (cell : ℕ → Ω → C)
    (used : ℕ → C → Prop) (x : Ω) (n m : ℕ)
    (hn : v23IsFirstTop cell used x n) (hm : v23IsFirstTop cell used x m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim (hm.2 n h hn.1)
  · exact h
  · exact False.elim (hn.2 m h hm.1)

theorem v23_first_top_whole_cell {Ω C : Type*} (cell : ℕ → Ω → C)
    (used : ℕ → C → Prop) (x y : Ω) (n : ℕ)
    (href : ∀ a b, a ≤ b → ∀ x y, cell b x = cell b y → cell a x = cell a y)
    (hxy : cell n x = cell n y) (hn : v23IsFirstTop cell used x n) :
    v23IsFirstTop cell used y n := by
  refine ⟨by rw [← hxy]; exact hn.1, ?_⟩
  intro j hj
  rw [← href j n (Nat.le_of_lt hj) x y hxy]
  exact hn.2 j hj

end OpenAI086
