import Mathlib
import OpenAI086.PaperSideMinimum
import OpenAI086.FiniteMultifamilyStops

/-! Proposition 5.8 (p.38): active path count from individual triple
counts and the exact cell-minimum reduction. The analytic estimates for
a fixed triple and the pair-smallness input are not established here. -/
namespace OpenAI086

theorem v26_active_union_count {I J : Type*} [DecidableEq J]
    (s : Finset I) (active : I → Finset J) (M : ℕ)
    (h : ∀ i ∈ s, (active i).card ≤ M) :
    (s.biUnion active).card ≤ s.card*M := by
  calc
    _ ≤ ∑ i ∈ s, (active i).card := finite_biUnion_card_le_sum s active
    _ ≤ ∑ i ∈ s, M := Finset.sum_le_sum h
    _ = _ := by simp [Nat.mul_comm]

theorem v26_min_subadd (η a b : ℝ) (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min η (a+b) ≤ min η a+min η b := by
  by_cases h1 : a ≤ η <;> by_cases h2 : b ≤ η
  · rw [min_eq_right h1, min_eq_right h2]; exact min_le_right _ _
  · rw [min_eq_right h1, min_eq_left (le_of_not_ge h2)]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge h1), min_eq_right h2]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge h1), min_eq_left (le_of_not_ge h2)]
    exact (min_le_left _ _).trans (by linarith)

theorem v26_min_sum {I : Type*} (s : Finset I) (a : I → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (ha : ∀ i ∈ s, 0 ≤ a i) :
    min η (∑ i ∈ s, a i) ≤ ∑ i ∈ s, min η (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [min_eq_right hη]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hnon : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hnon
    exact (v26_min_subadd η (a i) _ hη (ha i (Finset.mem_insert_self _ _)) hs).trans
      (add_le_add_left (ih hnon) _)

/-- The minimum stays at the original cell until after the complex
multilinear expansion; an absolute error is then charged at power one. -/
theorem v26_cell_min_expansion {I : Type*} (s : Finset I)
    (z : I → ℂ) (F e : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hF : F = (∑ i ∈ s, z i)+e) (hsmall : ‖F‖ ≤ η) :
    ‖F‖ ≤ (∑ i ∈ s, min η ‖z i‖)+‖e‖ := by
  have htri : ‖F‖ ≤ (∑ i ∈ s, ‖z i‖)+‖e‖ := by
    rw [hF]
    exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
  calc
    ‖F‖ ≤ min η ((∑ i ∈ s, ‖z i‖)+‖e‖) := le_min hsmall htri
    _ ≤ min η (∑ i ∈ s, ‖z i‖)+‖e‖ := v24_min_add_error _ _ _ (norm_nonneg _)
    _ ≤ _ := add_le_add_right (v26_min_sum s (fun i => ‖z i‖) η hη
      (fun i _ => norm_nonneg _)) _

end OpenAI086
