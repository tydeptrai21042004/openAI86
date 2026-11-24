import Mathlib
import OpenAI086.HeightLagTelescoping

/-! Lemma 8.3 p.68. Bound the number of discarded heights caused by
changes of either rank over an R-wide window. The rational subspace
construction and lifting in the saturated lattice are not included. -/
namespace OpenAI086

theorem v20_rank_change_indicator (a b : ℕ) (h : a ≤ b) :
    (if a < b then (1:ℝ) else 0) ≤ (b:ℝ)-(a:ℝ) := by
  split_ifs with hh
  · have h' : a+1 ≤ b := by omega
    have hr : (a:ℝ)+1 ≤ (b:ℝ) := by exact_mod_cast h'
    linarith
  · exact sub_nonneg.mpr (by exact_mod_cast h)

/-- One increasing rank sequence discards at most R*d heights. -/
theorem v20_rank_window_count (p : ℕ → ℕ) (R H d : ℕ)
    (hp : Monotone p) (hd : ∀ n, p n ≤ d) :
    (∑ h ∈ Finset.range H, if p h < p (h+R) then (1:ℝ) else 0) ≤ (R:ℝ)*d := by
  calc
    _ ≤ ∑ h ∈ Finset.range H, ((p (h+R):ℝ)-(p h:ℝ)) := by
      apply Finset.sum_le_sum
      intro h _
      exact v20_rank_change_indicator _ _ (hp (by omega))
    _ ≤ _ := finite_height_lag_budget (fun n => (p n:ℝ)) R H (d:ℝ)
      (fun n _ => Nat.cast_nonneg _) (fun n _ => by exact_mod_cast hd (H+n))

/-- The union of two rank-change exceptional sets costs at most 2Rd. -/
theorem v20_two_rank_window_count (p q : ℕ → ℕ) (R H d : ℕ)
    (hp : Monotone p) (hq : Monotone q)
    (hdp : ∀ n, p n ≤ d) (hdq : ∀ n, q n ≤ d) :
    (∑ h ∈ Finset.range H,
      if p h < p (h+R) ∨ q h < q (h+R) then (1:ℝ) else 0) ≤ 2*(R:ℝ)*d := by
  classical
  calc
    _ ≤ ∑ h ∈ Finset.range H,
        ((if p h < p (h+R) then (1:ℝ) else 0) +
         (if q h < q (h+R) then (1:ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases h1 : p h < p (h+R) <;> by_cases h2 : q h < q (h+R) <;> simp [h1,h2]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      linarith [v20_rank_window_count p R H d hp hdp, v20_rank_window_count q R H d hq hdq]

end OpenAI086
