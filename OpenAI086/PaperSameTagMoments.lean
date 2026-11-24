import Mathlib
import OpenAI086.PaperScaleRowSummation
import OpenAI086.PaperDetectionExtraction

/-! Lemma 6.6, pp.46–47: integer carry identity and the separated Fourier
moment estimate once spectator Bessel energies are available. -/
namespace OpenAI086

theorem v27_integer_carry (l : ℤ) (u t : ℝ) (n0 n1 nl : ℤ) :
    (u+(l : ℝ)*t-(nl : ℝ)) -
      ((1-(l : ℝ))*(u-(n0 : ℝ))+(l : ℝ)*(u+t-(n1 : ℝ))) =
      (((1-l)*n0+l*n1-nl : ℤ) : ℝ) := by
  push_cast
  ring

/-- The common ordinary quadratic factor cancels on all four slots. -/
theorem v27_common_quadratic (x t λ : ℝ) :
    -(λ*x^2)+3*λ*(x+t)^2-3*λ*(x+2*t)^2+λ*(x+3*t)^2 = 0 := by ring

/-- With the residual moment bounded by M, the separated test costs at
most M times the product of the two spectator Bessel norms. -/
theorem v27_same_tag_moment_bound {I : Type*} [Fintype I]
    (a b residual : I → ℂ) (M A B : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : ∀ i, ‖residual i‖ ≤ M)
    (ha : (∑ i, ‖a i‖^2) ≤ A^2) (hb : (∑ i, ‖b i‖^2) ≤ B^2) :
    ‖∑ i, residual i*a i*b i‖ ≤ M*A*B :=
  (norm_sum_le _ _).trans (v27_scale_row_sum a b residual A B M hA hB hM hm ha hb)

end OpenAI086
