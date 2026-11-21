import Mathlib

/-!
# Lemma 8.6: corrected interleaved cardinality-gap accounting

This is a proof of the *integer telescoping budget* underlying the
bad-density chain argument on manuscript page 70. It deliberately does
not claim to prove the full bad-density lemma (which also needs the
entry-rank and height estimates).

The original paper omitted the endpoint inclusion `P_N ⊆ C_N`; that
hypothesis is essential for nonnegative gaps at the last position.
-/

namespace OpenAI086

/-- The sum of ordered gaps is bounded by the overall endpoint gap,
provided every intermediate `c i` is at most the next `p (i+1)`.
The statement uses integers, so subtraction is not truncated. -/
theorem interleaved_gap_telescope (N : ℕ) (p c : ℕ → ℤ) :
    (∀ i < N, c i ≤ p (i + 1)) →
    (∑ i ∈ Finset.range (N + 1), (c i - p i)) ≤ c N - p 0 := by
  induction N with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hcp
      have hprefix :
          (∑ i ∈ Finset.range (n + 1), (c i - p i)) ≤ c n - p 0 :=
        ih (fun i hi => hcp i (by omega))
      have hstep : c n ≤ p (n + 1) := hcp n (by omega)
      rw [Finset.sum_range_succ]
      omega

/-- Under the corrected endpoint hypothesis, all cardinality-log gaps
are nonnegative, including the last one. -/
theorem interleaved_gap_nonnegative (N : ℕ) (p c : ℕ → ℤ)
    (hpc : ∀ i ≤ N, p i ≤ c i) :
    ∀ i ≤ N, 0 ≤ c i - p i := by
  intro i hi
  have h := hpc i hi
  omega

/-- The temporal gap budget is at most the common log-cardinality cap.
This is the exact telescoping step on page 70, with the final endpoint
included in `hpc`. The full bad-density estimate is not asserted here. -/
theorem interleaved_gap_budget (N : ℕ) (p c : ℕ → ℤ) (L : ℤ)
    (hpc : ∀ i ≤ N, p i ≤ c i)
    (hcp : ∀ i < N, c i ≤ p (i + 1))
    (hfirst : 0 ≤ p 0)
    (hlast : c N ≤ L) :
    (∑ i ∈ Finset.range (N + 1), (c i - p i)) ≤ L := by
  have h := interleaved_gap_telescope N p c hcp
  have hnonneg := interleaved_gap_nonnegative N p c hpc
  omega

end OpenAI086
