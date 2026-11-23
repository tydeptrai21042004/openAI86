import Mathlib

/-!
# Exact integer-arithmetic logarithmic bins (base 11/10)

The floor-log cardinality in manuscript Lemma 8.6 is based on 1.1.
For an integer n, the condition `(11/10)^(k+1) ≤ n` is equivalent to
`11^(k+1) ≤ n * 10^(k+1)` and therefore uses no floating-point logs.
We count such powers in an explicit finite search window 10(n+1).

The monotonicity proof below is unconditional. The separate assertion
that this search window contains *all* possible powers, and hence
identifies the true real floor-log for every n>0, is not proved here.
-/

namespace OpenAI086

/-- Count the integer power thresholds satisfied by the cardinality. -/
def integerLogBin11_10 (n : ℕ) : ℕ :=
  ((Finset.range (10 * (n + 1))).filter
    (fun k : ℕ => 11 ^ (k + 1) ≤ n * 10 ^ (k + 1))).card

/-- Crucial monotonicity under inclusion/cardinality increase, with no
real logarithm, rounding or numerical approximation in the proof. -/
theorem integer_log_bin_11_10_monotone : Monotone integerLogBin11_10 := by
  intro n m hnm
  unfold integerLogBin11_10
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hrange, hpow⟩ := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    have hbound := Finset.mem_range.mp hrange
    omega
  · exact hpow.trans (Nat.mul_le_mul_right (10 ^ (k + 1)) hnm)

/-- An upper bound on the cardinality induces an upper bound on the
integer bin index. -/
theorem integer_log_bin_card_le
    {α : Type*} (S : Finset α) (M : ℕ) (hSM : S.card ≤ M) :
    integerLogBin11_10 S.card ≤ integerLogBin11_10 M :=
  integer_log_bin_11_10_monotone hSM

end OpenAI086
