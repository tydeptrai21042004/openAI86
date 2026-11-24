import Mathlib
import OpenAI086.PaperTinyGapClosure

/-! Lemma 8.2: the integral denominator lower bound, coefficient bound
for Cramer ratios, and the ensuing tiny-space gap closure. The selection
of an invertible minor and the numerator height bound remain separate. -/
namespace OpenAI086

theorem v20_nonzero_integer_abs_cast (d : ℤ) (hd : d ≠ 0) : 1 ≤ |(d : ℝ)| := by
  have hi : (1 : ℤ) ≤ |d| := by
    rcases lt_or_gt_of_ne hd with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  exact_mod_cast hi

/-- Integral Cramer numerators, with a common nonzero integral determinant.
This proves the division step rather than assuming bounded coefficients. -/
theorem v20_cramer_ratio_l1 {I : Type*} [Fintype I]
    (d : ℤ) (hd : d ≠ 0) (num : I → ℤ) (c : I → ℝ) (M : ℝ)
    (hc : ∀ i, (d : ℝ)*c i = (num i : ℝ))
    (hnum : ∀ i, |(num i : ℝ)| ≤ M) :
    (∑ i, |c i|) ≤ (Fintype.card I : ℝ)*M := by
  classical
  have hd' := v20_nonzero_integer_abs_cast d hd
  calc
    _ ≤ ∑ _i : I, M := by
      apply Finset.sum_le_sum
      intro i _
      have h1 : |(d : ℝ)|*|c i| = |(num i : ℝ)| := by rw [← abs_mul, hc]
      have h2 := mul_le_mul_of_nonneg_right hd' (abs_nonneg (c i))
      rw [one_mul, h1] at h2
      exact h2.trans (hnum i)
    _ = _ := by simp

/-- Combine the explicit determinant-division bound with the gap argument. -/
theorem v20_cramer_tiny_closure {I : Type*} [Fintype I]
    (d : ℤ) (hd : d ≠ 0) (num : I → ℤ) (c v : I → ℝ)
    (M δ A x : ℝ) (hδ : 0 ≤ δ)
    (hc : ∀ i, (d : ℝ)*c i = (num i : ℝ))
    (hnum : ∀ i, |(num i : ℝ)| ≤ M) (hv : ∀ i, |v i| ≤ δ)
    (hx : x = ∑ i, c i*v i) (hsep : ((Fintype.card I : ℝ)*M)*δ < A)
    (hgap : |x| ≤ δ ∨ A ≤ |x|) : |x| ≤ δ :=
  v19_tiny_gap_forces_small c v δ ((Fintype.card I : ℝ)*M) A x hδ hv
    (v20_cramer_ratio_l1 d hd num c M hc hnum) hx hsep hgap

/-- Product bound for a determinant expansion term (after clearing
rational denominators). The full minor selection is not asserted. -/
theorem v20_bounded_product {I : Type*} [Fintype I]
    (a : I → ℝ) (H : ℝ) (ha : ∀ i, |a i| ≤ H) :
    (∏ i, |a i|) ≤ H^(Fintype.card I) := by
  classical
  calc
    _ ≤ ∏ _i : I, H := Finset.prod_le_prod (fun i _ => abs_nonneg (a i)) (fun i _ => ha i)
    _ = _ := by simp

/-- Actual determinant estimate via the Leibniz expansion, uniform in all
matrix entries. The permutation cardinal is k!, without a dimension loss
beyond the usual determinant bound. -/
theorem v20_matrix_det_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (H : ℝ) (hA : ∀ i j, |A i j| ≤ H) :
    |A.det| ≤ (Fintype.card (Equiv.Perm I) : ℝ)*H^(Fintype.card I) := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm I, |(((σ.sign : ℤˣ) : ℤ) : ℝ) * (∏ i, A (σ i) i)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le (Finset.univ : Finset (Equiv.Perm I))
          (fun σ => (((σ.sign : ℤˣ) : ℤ) : ℝ) * (∏ i, A (σ i) i))
    _ ≤ ∑ _σ : Equiv.Perm I, H^(Fintype.card I) := by
      apply Finset.sum_le_sum
      intro σ _
      have h := v20_bounded_product (fun i => A (σ i) i) H (fun i => hA (σ i) i)
      have hp : |∏ i, A (σ i) i| = ∏ i, |A (σ i) i| := by
        first | exact Finset.abs_prod _ _ | simp [abs_prod] | exact?
      rw [← hp] at h
      rcases Int.units_eq_one_or σ.sign with hσ | hσ
      · simpa [hσ] using h
      · simpa [hσ] using h
    _ = _ := by simp

/-- Lemma 8.2 packet-width argument: six K-spaced exceptional starts
cannot lie inside the open interval of length at most 4K. -/
theorem v20_packet_no_six_starts (K W τ α b₀ b₅ : ℝ)
    (hK : 0 < K) (hw : W+2*τ ≤ K)
    (hlo : α-K-τ < b₀) (hhi : b₅ < α+W+2*K+τ)
    (hspacing : b₀+5*K ≤ b₅) : False := by linarith

end OpenAI086
