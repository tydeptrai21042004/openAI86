import Mathlib
import OpenAI086.FiniteRowCauchySchwarz

/-! Lemma 5.1, p.31: conclude the absolute scale sum from the clump
coefficient and the two genuine row energy estimates. The analytic proof
of the row estimates and the selection of clumps are still required. -/
namespace OpenAI086

theorem v27_scale_row_sum {I : Type*} [Fintype I]
    (a b c : I → ℂ) (A B δ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ δ)
    (hc : ∀ i, ‖c i‖ ≤ δ)
    (ha : (∑ i, ‖a i‖^2) ≤ A^2) (hb : (∑ i, ‖b i‖^2) ≤ B^2) :
    (∑ i, ‖c i*a i*b i‖) ≤ δ*A*B := by
  let S := ∑ i, ‖a i‖*‖b i‖
  have hs : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq : S^2 ≤ (A*B)^2 := by
    calc
      S^2 ≤ (∑ i, ‖a i‖^2)*(∑ i, ‖b i‖^2) :=
        finite_row_cauchy_schwarz (fun i => ‖a i‖) (fun i => ‖b i‖)
      _ ≤ A^2*B^2 := mul_le_mul ha hb (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
      _ = (A*B)^2 := by ring
  have hAB : 0 ≤ A*B := mul_nonneg hA hB
  have hS : S ≤ A*B := by
    by_contra hn
    have hlt : A*B < S := lt_of_not_ge hn
    have hpos : 0 < (S-A*B)*(S+A*B) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    nlinarith
  calc
    _ ≤ ∑ i, δ*(‖a i‖*‖b i‖) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hc i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = δ*S := by rw [Finset.mul_sum]
    _ ≤ δ*(A*B) := mul_le_mul_of_nonneg_left hS hd
    _ = _ := by ring

/-- The test at the representative frequency recovers the combined
coefficient, provided the off-clump and approximation errors are bounded. -/
theorem v27_clump_coefficient (z c e : ℂ) (w δ ε : ℝ)
    (hw : 0 < w) (hz : ‖z‖ ≤ δ) (he : ‖e‖ ≤ ε)
    (h : z = (w : ℂ)*c+e) : ‖c‖ ≤ (δ+ε)/w := by
  have heq : (w : ℂ)*c = z-e := by rw [h]; abel
  have hh := norm_sub_le z e
  rw [← heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw] at hh
  apply (le_div_iff₀ hw).2
  rw [mul_comm]
  linarith

end OpenAI086
