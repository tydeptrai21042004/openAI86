import Mathlib

/-!
# Lemma 8.6, page 70: the actual height-lag telescoping identity

For a scalar sequence `p` (in the application: the floor-log cardinalities
of a nested family at fixed spatial position), the total lagged increments
across H heights collapse to just the first and last Δ values. No monotonicity
is required for the IDENTITY; nonnegative/bounded values are used only to
bound the boundary terms. This is precisely the Δ L term that occurs in
the manuscript's bad-density counting budget. It does not prove Lemma 8.6:
entry-rank and exceptional-primary budgets remain separate obligations.

Independent new code; no reference formalization is imported.
-/

namespace OpenAI086

/-- Telescoping in one contiguous integer block. -/
theorem finite_lag_increment_block (p : ℕ → ℝ) (start lag : ℕ) :
    (∑ r ∈ Finset.range lag,
      (p (start + r + 1) - p (start + r))) =
      p (start + lag) - p start := by
  induction lag with
  | zero => simp
  | succ lag ih =>
      rw [Finset.sum_range_succ, ih]
      have h : start + lag + 1 = start + (lag + 1) := by omega
      rw [h]
      ring

/-- The delayed difference sum has no dependence on the total number of
heights except via the two Δ-element boundary blocks. -/
theorem finite_height_lag_telescoping (p : ℕ → ℝ) (lag H : ℕ) :
    (∑ h ∈ Finset.range H, (p (h + lag) - p h)) =
      ∑ r ∈ Finset.range lag, (p (H + r) - p r) := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ, ih]
      have hshift :
          (∑ r ∈ Finset.range lag, (p (H + 1 + r) - p (H + r))) =
            p (H + lag) - p H := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          finite_lag_increment_block p H lag
      calc
        (∑ r ∈ Finset.range lag, (p (H + r) - p r)) +
            (p (H + lag) - p H) =
          ∑ r ∈ Finset.range lag,
            ((p (H + r) - p r) +
              (p (H + 1 + r) - p (H + r))) := by
                rw [← Finset.sum_add_distrib, hshift]
        _ = ∑ r ∈ Finset.range lag, (p (H + 1 + r) - p r) := by
              apply Finset.sum_congr rfl
              intro r _
              ring

/-- Signed lagged increments cost at most `lag * cap` when the final
boundary samples lie below `cap` and initial samples are nonnegative. -/
theorem finite_height_lag_budget (p : ℕ → ℝ)
    (lag H : ℕ) (cap : ℝ)
    (hfirst : ∀ r < lag, 0 ≤ p r)
    (hlast : ∀ r < lag, p (H + r) ≤ cap) :
    (∑ h ∈ Finset.range H, (p (h + lag) - p h)) ≤
      (lag : ℝ) * cap := by
  rw [finite_height_lag_telescoping]
  calc
    (∑ r ∈ Finset.range lag, (p (H + r) - p r)) ≤
        ∑ _r ∈ Finset.range lag, cap := by
          apply Finset.sum_le_sum
          intro r hr
          have hrlt : r < lag := Finset.mem_range.mp hr
          have ha := hfirst r hrlt
          have hb := hlast r hrlt
          linarith
    _ = (lag : ℝ) * cap := by simp

/-- With the index convention from the PDF, the range `lag ≤ h < lag+H`
incurs exactly the same boundary cost. -/
theorem finite_height_lag_shifted_budget (p : ℕ → ℝ)
    (lag H : ℕ) (cap : ℝ)
    (hfirst : ∀ r < lag, 0 ≤ p r)
    (hlast : ∀ r < lag, p (H + r) ≤ cap) :
    (∑ h ∈ Finset.range H, (p (lag + h) - p h)) ≤
      (lag : ℝ) * cap := by
  have h := finite_height_lag_budget p lag H cap hfirst hlast
  simpa only [Nat.add_comm lag] using h

end OpenAI086
