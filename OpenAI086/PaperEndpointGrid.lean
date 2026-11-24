import Mathlib
import OpenAI086.PaperEndpointSeparation

/-! Last-separating-depth grid in Lemma 6.5. Work with a refining cell
label family; the depth of a term may vary independently of all others. -/
namespace OpenAI086

theorem v23_last_separation {T : ℕ} (sep : ℕ → Prop)
    (h : ∃ n ≤ T, sep n) : ∃ d ≤ T, sep d ∧ ∀ n ≤ T, sep n → n ≤ d := by
  classical
  let S := (Finset.range (T+1)).filter sep
  have hS : S.Nonempty := by
    obtain ⟨n, hn, hs⟩ := h
    exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩⟩
  refine ⟨S.max' hS, ?_, ?_, ?_⟩
  · have hm := (Finset.mem_filter.mp (S.max'_mem hS)).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  · exact (Finset.mem_filter.mp (S.max'_mem hS)).2
  · intro n hn hs
    exact Finset.le_max' S n (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩)

/-- Every nonempty overlap at an allowed depth is constant on the last
separation grid. Empty intersections make no contribution. -/
theorem v23_overlap_grid_constant {Ω C : Type*}
    (cell : ℕ → Ω → C) (d a b : ℕ) (A B : C)
    (href : ∀ i j, i ≤ j → ∀ x y, cell j x = cell j y → cell i x = cell i y)
    (ha : a ≤ d) (hb : b ≤ d) (x y : Ω) (hxy : cell d x = cell d y) :
    (cell a x = A ∧ cell b x = B) ↔ (cell a y = A ∧ cell b y = B) := by
  rw [href a d ha x y hxy, href b d hb x y hxy]

end OpenAI086
