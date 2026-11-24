import Mathlib

/-! Lemma 8.2, page 68: once a bounded coefficient representation in tiny
vectors is obtained, the gap forces its evaluation into the tiny range.
The rational-height basis and Cramer coefficient bound are still missing. -/
namespace OpenAI086

theorem v19_tiny_span_evaluation {I : Type*} [Fintype I]
    (c v : I → ℝ) (δ M : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ δ) (hc : (∑ i, |c i|) ≤ M) :
    |∑ i, c i*v i| ≤ M*δ := by
  classical
  calc
    _ ≤ ∑ i, |c i*v i| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset I) (fun i => c i*v i))
    _ ≤ ∑ i, |c i|*δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = (∑ i, |c i|)*δ := by rw [Finset.sum_mul]
    _ ≤ M*δ := mul_le_mul_of_nonneg_right hc hδ

/-- The exact dichotomy argument in the second assertion of Lemma 8.2. -/
theorem v19_tiny_gap_forces_small {I : Type*} [Fintype I]
    (c v : I → ℝ) (δ M A x : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ δ) (hc : (∑ i, |c i|) ≤ M)
    (hx : x = ∑ i, c i*v i) (hsep : M*δ < A)
    (hgap : |x| ≤ δ ∨ A ≤ |x|) : |x| ≤ δ := by
  have h := v19_tiny_span_evaluation c v δ M hδ hv hc
  rw [← hx] at h
  rcases hgap with hs | hl
  · exact hs
  · linarith

end OpenAI086
