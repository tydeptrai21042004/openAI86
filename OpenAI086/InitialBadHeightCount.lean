import Mathlib

/-!
# Lemma 8.6: exact number of automatically bad initial heights

The manuscript declares every height h < Δ bad. These are additional
to the shifted-window count in the V10--V12 bridge. We count them
exactly rather than adding an unspecified O(Δ) error.
-/

namespace OpenAI086

/-- Number of indices `h < J` lying in the initial bad-height zone
`h < lag`, expressed as a real sum for direct use in density budgets. -/
theorem initial_bad_height_exact (J lag : ℕ) :
    (∑ h ∈ Finset.range J,
      if h < lag then (1 : ℝ) else 0) = (min J lag : ℝ) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : J < lag
      · have hm : min (J + 1) lag = min J lag + 1 := by omega
        simp only [if_pos h, hm, Nat.cast_add, Nat.cast_one]
        ring
      · have hm : min (J + 1) lag = min J lag := by omega
        simp only [if_neg h, hm, add_zero]

/-- An initial height is bad by definition, regardless of the main
rank/gap and exceptional-density tests. This inequality is valid for
any additional nonnegative bad-height indicator on later heights. -/
theorem initial_bad_height_lower_bound (J lag : ℕ)
    (b : ℕ → ℝ) (hnonneg : ∀ h, 0 ≤ b h) :
    (min J lag : ℝ) ≤
      ∑ h ∈ Finset.range J,
        (if h < lag then (1 : ℝ) else b h) := by
  have hterm :
      (∑ h ∈ Finset.range J,
        if h < lag then (1 : ℝ) else 0) ≤
      ∑ h ∈ Finset.range J,
        (if h < lag then (1 : ℝ) else b h) := by
    apply Finset.sum_le_sum
    intro h _
    by_cases hh : h < lag
    · simp [hh]
    · simpa [hh] using hnonneg h
  rw [initial_bad_height_exact] at hterm
  exact hterm

end OpenAI086
