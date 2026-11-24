import Mathlib

/-! Lemma 6.3 (pp.42–43): monotone score episodes and deterministic
winner-shift injection in the geometric-delay marking argument.
The probability measure and union bound over path situations remain open. -/
namespace OpenAI086

def v26Marked {V : Type*} (score : V → ℤ) (v : V) (gap : ℤ) : Prop :=
  ∀ w, w ≠ v → score w+gap ≤ score v

theorem v26_marked_unique {V : Type*} (score : V → ℤ) (v w : V) (g : ℤ)
    (hg : 0 < g) (hv : v26Marked score v g) (hw : v26Marked score w g) : v = w := by
  by_contra h
  have h1 := hv w (Ne.symm h)
  have h2 := hw v h
  omega

/-- At a fixed top score, a marked winner cannot change under monotone
competitor scores, even if intermediate times are unmarked. -/
theorem v26_fixed_top_winner {V : Type*} (s t : V → ℤ) (v w : V) (g : ℤ)
    (hg : 0 < g) (hst : ∀ u, s u ≤ t u) (htop : s v = t w)
    (hw : v26Marked t w g) : v = w := by
  by_contra h
  have h1 := hst v
  have h2 := hw v h
  omega

/-- If a winner's margin has failed while its top score stays fixed,
monotonicity prevents its restoration at that top score. -/
theorem v26_mark_failure_persists {V : Type*} (s t : V → ℤ)
    (v w : V) (g : ℤ) (hst : ∀ u, s u ≤ t u)
    (htop : s v = t v) (hw : w ≠ v) (hbad : s v < s w+g) :
    ¬ v26Marked t v g := by
  intro h
  have h1 := h w hw
  have h2 := hst w
  omega

/-- Raising a maximizer's score by the gap produces a marked winner. -/
theorem v26_shift_winner_marked {V : Type*} [DecidableEq V]
    (s : V → ℤ) (v : V) (g : ℤ) (hv : ∀ w, s w ≤ s v) :
    v26Marked (Function.update s v (s v+g)) v g := by
  intro w hw
  rw [Function.update_of_ne hw, Function.update_self]
  exact add_le_add_right (hv w) g

/-- The canonical-winner shift is injective: its image identifies the
raised coordinate, then cancellation recovers every original score. -/
theorem v26_winner_shift_injective {V : Type*} [DecidableEq V]
    (winner : (V → ℤ) → V) (g : ℤ) (hg : 0 < g)
    (hm : ∀ s w, s w ≤ s (winner s)) :
    Function.Injective (fun s : V → ℤ => Function.update s (winner s) (s (winner s)+g)) := by
  intro s t he
  have hs := v26_shift_winner_marked s (winner s) g (hm s)
  have ht := v26_shift_winner_marked t (winner t) g (hm t)
  rw [← he] at ht
  have hw := v26_marked_unique _ _ _ g hg hs ht
  funext w
  have hh := congrFun he w
  rw [← hw] at hh
  by_cases h : w = winner s
  · subst w
    simp only [Function.update_self] at hh
    omega
  · simpa only [Function.update_of_ne h] using hh

end OpenAI086
