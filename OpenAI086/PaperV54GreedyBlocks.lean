import Mathlib
import OpenAI086.SparseBlockAccounting

/-! Lemma 9.1, p.83: construct consecutive greedy counting blocks from
ordered scale occurrences, not merely a bound assuming such blocks exist.
The recursion processes the list right-to-left; reverse the input and each
output block and reverse the block order to obtain the left-to-right rule.
All blocks except the first (the unfinished block) exceed cap - δ. -/
namespace OpenAI086

noncomputable def v54GreedyBlocks {S : Type*} (w : S → ℝ) (cap : ℝ) :
    List S → List (List S)
  | [] => []
  | x :: xs =>
    match v54GreedyBlocks w cap xs with
    | [] => [[x]]
    | b :: bs => if w x + (b.map w).sum ≤ cap then (x :: b) :: bs
        else [x] :: b :: bs

/-- Every occurrence survives exactly once, in its original order. -/
theorem v54_greedy_flatten {S : Type*} (w : S → ℝ) (cap : ℝ) (xs : List S) :
    (v54GreedyBlocks w cap xs).flatten = xs := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [v54GreedyBlocks]
    cases h : v54GreedyBlocks w cap xs with
    | nil =>
      try rw [h] at ih
      simpa using congrArg (List.cons x) ih
    | cons b bs =>
      try rw [h] at ih
      split_ifs <;> simpa using congrArg (List.cons x) ih

/-- Every block has mass at most cap, and every completed block has mass
strictly larger than cap - δ. The only possibly unfinished block is the
first one. This proves the hypotheses of the paper's block accounting. -/
theorem v54_greedy_mass_bounds {S : Type*} (w : S → ℝ) (cap δ : ℝ)
    (hδ : δ ≤ cap) (xs : List S) (hw : ∀ x ∈ xs, w x ≤ δ) :
    (∀ b ∈ v54GreedyBlocks w cap xs, (b.map w).sum ≤ cap) ∧
    (∀ b ∈ (v54GreedyBlocks w cap xs).tail, cap-δ < (b.map w).sum) := by
  classical
  induction xs with
  | nil => simp [v54GreedyBlocks]
  | cons x xs ih =>
    have hx := hw x (by simp)
    have ht := ih (fun y hy => hw y (by simp [hy]))
    simp only [v54GreedyBlocks]
    cases h : v54GreedyBlocks w cap xs with
    | nil =>
      constructor
      · intro b hb
        simp at hb
        subst b
        simpa using hx.trans hδ
      · simp
    | cons b bs =>
      try rw [h] at ht
      split_ifs with hfit
      · constructor
        · intro a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · simpa using hfit
          · exact ht.1 a (by simp [ha])
        · simpa using ht.2
      · constructor
        · intro a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · simpa using hx.trans hδ
          · exact ht.1 a ha
        · intro a ha
          change a ∈ b :: bs at ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · linarith
          · exact ht.2 a (by simpa using ha)

end OpenAI086
