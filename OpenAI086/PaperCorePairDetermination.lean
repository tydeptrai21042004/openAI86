import Mathlib

/-! Proposition 9.2: solve the two linear frequency tests for the two
remaining role values. Shift and residual errors are included in E.
The graph separation and sparse-count hypotheses must still be derived. -/
namespace OpenAI086

theorem v23_two_frequency_equations (a b x y Q T E : ℝ)
    (hab : 1 ≤ |b-a|) (ha : |a| ≤ 3) (hb : |b| ≤ 3)
    (hE : 0 ≤ E) (hQ : x+y=Q) (hT : a*x+b*y=T)
    (hq : |Q| ≤ E) (ht : |T| ≤ E) : |x| ≤ 4*E ∧ |y| ≤ 4*E := by
  have hx : (b-a)*x=b*Q-T := by rw [← hQ, ← hT]; ring
  have hy : (b-a)*y=T-a*Q := by rw [← hQ, ← hT]; ring
  constructor
  · have h1 : |x| ≤ |(b-a)*x| := by
      rw [abs_mul]; simpa using mul_le_mul_of_nonneg_right hab (abs_nonneg x)
    rw [hx] at h1
    have h2 := abs_sub (b*Q) T
    rw [abs_mul] at h2
    have h3 := mul_le_mul hb hq (abs_nonneg Q) (by norm_num : (0:ℝ) ≤ 3)
    linarith
  · have h1 : |y| ≤ |(b-a)*y| := by
      rw [abs_mul]; simpa using mul_le_mul_of_nonneg_right hab (abs_nonneg y)
    rw [hy] at h1
    have h2 := abs_sub T (a*Q)
    rw [abs_mul] at h2
    have h3 := mul_le_mul ha hq (abs_nonneg Q) (by norm_num : (0:ℝ) ≤ 3)
    linarith

end OpenAI086
