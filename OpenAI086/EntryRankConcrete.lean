import Mathlib
import OpenAI086.EntryRankSummation

/-!
# OpenAI #086, Lemma 8.5: incidence bound from entry ranks

The prior module assumed the `A/r` estimate for each rank. Here we
prove that estimate from the two explicit hypotheses appearing in the
paper: at most `A` exceptional occurrences of each ranked label, and
any set containing the label of rank `r` has size at least `r+1`.

This covers the *analytic arithmetic step* of Lemma 8.5. Constructing a
rank-order equivalence from a chain of finite sets is a separate open
formalization step, so the full Lemma 8.5 is NOT claimed proved.
-/

namespace OpenAI086

/-- A concrete ranked version of Lemma 8.5. Each `active t r` means that
rank `r` belongs to the exceptional set `X_t`; `size t` is `|S_t|`.
The entry-rank hypothesis ensures `r+1 ≤ |S_t|` at each occurrence. -/
theorem ranked_exceptional_density_le
    (T M : ℕ) (A : ℝ)
    (active : Fin T → Fin M → Prop) (size : Fin T → ℕ)
    (hsize : ∀ (t : Fin T) (r : Fin M), active t r → r.val + 1 ≤ size t)
    (hinc : ∀ r : Fin M,
      (∑ t : Fin T, if active t r then (1 : ℝ) else 0) ≤ A) :
    (∑ t : Fin T, ∑ r : Fin M,
      if active t r then (1 : ℝ) / (size t : ℝ) else 0) ≤
      A * (∑ r : Fin M, (1 : ℝ) / ((r.val + 1 : ℕ) : ℝ)) := by
  classical
  have hper (r : Fin M) :
      (∑ t : Fin T, if active t r then (1 : ℝ) / (size t : ℝ) else 0) ≤
        A / (((r.val + 1 : ℕ) : ℝ)) := by
    have hterm (t : Fin T) :
        (if active t r then (1 : ℝ) / (size t : ℝ) else 0) ≤
          (if active t r then (1 : ℝ) else 0) *
            (1 / (((r.val + 1 : ℕ) : ℝ))) := by
      by_cases h : active t r
      · simp only [if_pos h, one_mul]
        have hpos : (0 : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by positivity
        have hbound : ((r.val + 1 : ℕ) : ℝ) ≤ (size t : ℝ) := by
          exact_mod_cast hsize t r h
        exact one_div_le_one_div_of_le hpos hbound
      · simp [h]
    calc
      (∑ t : Fin T, if active t r then (1 : ℝ) / (size t : ℝ) else 0) ≤
          ∑ t : Fin T,
            (if active t r then (1 : ℝ) else 0) *
              (1 / (((r.val + 1 : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum
          intro t _
          exact hterm t
      _ = (∑ t : Fin T, if active t r then (1 : ℝ) else 0) *
          (1 / (((r.val + 1 : ℕ) : ℝ))) := by rw [Finset.sum_mul]
      _ ≤ A * (1 / (((r.val + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (hinc r) (by positivity)
      _ = A / (((r.val + 1 : ℕ) : ℝ)) := by ring
  exact entry_rank_double_count T M A
    (fun t r => if active t r then (1 : ℝ) / (size t : ℝ) else 0)
    hper

end OpenAI086
