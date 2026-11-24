import Mathlib
import OpenAI086.PaperCompressionMoments

/-! Lemma 3.4: first-stop construction on a finite refining family.
The depth is part of the cut label. No measure or doubling assumption is
needed for the partition construction itself. -/
namespace OpenAI086

variable {Ω C : Type*}

def v21StopEligible (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) (n : ℕ) : Prop :=
  (n ≤ T ∧ stop n (cell n x)) ∨ n = T

noncomputable def v21FirstStop (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) : ℕ := by
  classical
  exact Nat.find (show ∃ n, v21StopEligible cell stop T x n from ⟨T, Or.inr rfl⟩)

theorem v21_first_stop_eligible (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) : v21StopEligible cell stop T x (v21FirstStop cell stop T x) := by
  classical
  unfold v21FirstStop
  exact Nat.find_spec _

theorem v21_first_stop_le (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) (n : ℕ) (h : v21StopEligible cell stop T x n) :
    v21FirstStop cell stop T x ≤ n := by
  classical
  unfold v21FirstStop
  exact Nat.find_min' _ h

theorem v21_first_stop_horizon (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) : v21FirstStop cell stop T x ≤ T :=
  v21_first_stop_le cell stop T x T (Or.inr rfl)

theorem v21_no_earlier_stop (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) (n : ℕ) (hn : n < v21FirstStop cell stop T x) :
    ¬ stop n (cell n x) := by
  intro hs
  have hT := v21_first_stop_horizon cell stop T x
  have h := v21_first_stop_le cell stop T x n (Or.inl ⟨by omega, hs⟩)
  omega

/-- A whole cell at the first cut depth has the same stopping depth.
Refinement is expressed by equality of finer labels implying equality of
all coarser labels. Thus this applies to actual dyadic partitions too. -/
theorem v21_first_stop_constant_on_cut
    (cell : ℕ → Ω → C) (stop : ℕ → C → Prop) (T : ℕ)
    (href : ∀ a b, a ≤ b → ∀ x y, cell b x = cell b y → cell a x = cell a y)
    (x y : Ω) (he : cell (v21FirstStop cell stop T x) x =
      cell (v21FirstStop cell stop T x) y) :
    v21FirstStop cell stop T y = v21FirstStop cell stop T x := by
  let n := v21FirstStop cell stop T x
  let m := v21FirstStop cell stop T y
  have hn : v21StopEligible cell stop T y n := by
    rcases v21_first_stop_eligible cell stop T x with h | h
    · exact Or.inl ⟨h.1, by rw [← he]; exact h.2⟩
    · exact Or.inr h
  have hmn : m ≤ n := v21_first_stop_le cell stop T y n hn
  have hm : v21StopEligible cell stop T x m := by
    rcases v21_first_stop_eligible cell stop T y with h | h
    · exact Or.inl ⟨h.1, by rw [href m n hmn x y he]; exact h.2⟩
    · exact Or.inr h
  exact le_antisymm hmn (v21_first_stop_le cell stop T x m hm)

noncomputable def v21CutLabel (cell : ℕ → Ω → C) (stop : ℕ → C → Prop)
    (T : ℕ) (x : Ω) : ℕ × C :=
  (v21FirstStop cell stop T x, cell (v21FirstStop cell stop T x) x)

/-- The fibers of the cut label are exactly entire cells at their cut depth. -/
theorem v21_cut_fiber_eq_cell (cell : ℕ → Ω → C) (stop : ℕ → C → Prop) (T : ℕ)
    (href : ∀ a b, a ≤ b → ∀ x y, cell b x = cell b y → cell a x = cell a y)
    (x y : Ω) : v21CutLabel cell stop T y = v21CutLabel cell stop T x ↔
      cell (v21FirstStop cell stop T x) y = cell (v21FirstStop cell stop T x) x := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    change v21FirstStop cell stop T y = v21FirstStop cell stop T x at hfst
    change cell (v21FirstStop cell stop T y) y = cell (v21FirstStop cell stop T x) x at hsnd
    rwa [hfst] at hsnd
  · intro h
    have hn := v21_first_stop_constant_on_cut cell stop T href x y h.symm
    simp [v21CutLabel, hn, h]

/-- Orthogonal refitting preserves every moment against a vector in the
projection range. This is the local identity to be summed over cut cells. -/
theorem v21_refit_preserves_moment {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (P : X →+ X)
    (hs : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v))
    (z φ : X) (hφ : P φ = φ) : inner ℝ (P z) φ = inner ℝ z φ := by
  rw [hs, hφ]

end OpenAI086
