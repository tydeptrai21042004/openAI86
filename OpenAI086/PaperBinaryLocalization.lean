import Mathlib

/-! Proposition 6.8, pp.49–50: exact binary decomposition for a linear
slot, valid at every node with a different linear map and input. A full
color-search construction and analytic error control are still needed. -/
namespace OpenAI086

inductive V27SplitTree (E : Type*) where
  | leaf : E → V27SplitTree E
  | node : V27SplitTree E → V27SplitTree E → V27SplitTree E

namespace V27SplitTree
variable {E : Type*} [AddCommGroup E]

def total : V27SplitTree E → E
  | leaf x => x
  | node l r => l.total+r.total

def leaves : V27SplitTree E → List E
  | leaf x => [x]
  | node l r => l.leaves ++ r.leaves

theorem v27_leaf_sum (T : V27SplitTree E) : T.leaves.sum = T.total := by
  induction T with
  | leaf x => simp [leaves,total]
  | node l r hl hr => simp [leaves,total,List.sum_append,hl,hr]

end V27SplitTree

/-- Split a linear slot into its primal and residual without introducing
an approximation or assuming that Q is idempotent. -/
theorem v27_localization_split {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H : E →ₗ[ℂ] ℂ) (Q : E →ₗ[ℂ] E) (x : E) :
    H x = H (Q x)+H (x-Q x) := by
  rw [map_sub]
  ring

/-- Telescope successive filter insertions, charging only their absolute
errors. No estimate for the remaining main term is hidden in this lemma. -/
theorem v27_localization_error (n : ℕ) (F : ℕ → ℂ) (e : ℕ → ℝ)
    (h : ∀ j < n, ‖F (j+1)-F j‖ ≤ e j) :
    ‖F n-F 0‖ ≤ ∑ j ∈ Finset.range n, e j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : ‖F n-F 0‖ ≤ ∑ j ∈ Finset.range n, e j :=
      ih (fun j hj => h j (by omega))
    calc
      _ = ‖(F (n+1)-F n)+(F n-F 0)‖ := by congr 1 <;> abel
      _ ≤ ‖F (n+1)-F n‖+‖F n-F 0‖ := norm_add_le _ _
      _ ≤ _ := by linarith [h n (by omega)]

end OpenAI086
