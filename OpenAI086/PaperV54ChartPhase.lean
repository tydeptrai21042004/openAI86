import OpenAI086.PaperV51WeylReturnAlgebra

/-! Lemma 4.3, pp.16–17: the exact chart phase increment behind the
translation identity. The lattice reindexing and Gevrey L¹ error are
still required for the full analytic recurrence. -/
namespace OpenAI086

/-- For u = Vz, w = u-n and Vh = m+d, the chart phase increment
splits into a frequency term, a small residual, a lattice term and a
constant. The expression is valid for nonsymmetric C. -/
theorem v54_chart_bilinear_increment {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (u n m d : E) :
    C (u+m+d) (u-n+d) - C u (u-n) =
      C u (m+d) - (C u m - C m u) + C d (u-n) - C m n +
      C m d + C d d := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

/-- Add the symmetric ordinary quadratic and linear phases. The terms
linear in z are precisely Ω(h,m)·z from the manuscript. -/
theorem v54_chart_total_increment {X E : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (B : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (V : X →ₗ[ℝ] E) (b : X →ₗ[ℝ] ℝ)
    (z h : X) (n m d : E) (hV : V h = m+d)
    (hB : B h z = B z h) :
    (B (z+h) (z+h) + b (z+h) + C (V (z+h)) (V (z+h)-(n+m))) -
      (B z z + b z + C (V z) (V z-n)) =
      (2*B z h + C (V z) (V h) - (C (V z) m - C m (V z))) +
      C d (V z-n) - C m n + (B h h + b h + C m d + C d d) := by
  simp only [map_add, hV, LinearMap.add_apply, map_sub]
  rw [hB]
  ring

/-- When C(m,n) is integral, this term vanishes in the chart phase
modulo the integer lattice. The witness is the actual difference. -/
theorem v54_chart_increment_mod_integer {X E : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (B : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (V : X →ₗ[ℝ] E) (b : X →ₗ[ℝ] ℝ)
    (z h : X) (n m d : E) (hV : V h = m+d) (hB : B h z = B z h)
    (k : ℤ) (hk : C m n = (k:ℝ)) :
    (B (z+h) (z+h) + b (z+h) + C (V (z+h)) (V (z+h)-(n+m))) -
      (B z z + b z + C (V z) (V z-n)) -
      ((2*B z h + C (V z) (V h) - (C (V z) m - C m (V z))) +
        C d (V z-n) + (B h h + b h + C m d + C d d)) = -(k:ℝ) := by
  rw [v54_chart_total_increment C B V b z h n m d hV hB, hk]
  ring

end OpenAI086
