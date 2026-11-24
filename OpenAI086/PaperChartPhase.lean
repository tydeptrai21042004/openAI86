import Mathlib

/-! Lemma 4.4, p.19: phase splitting for actual bilinear forms.
The periodic Fourier expansion and Gevrey estimates are not assumed proven. -/
namespace OpenAI086
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Symmetric chart phase with w = u - n. -/
theorem v25_symmetric_chart_phase (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (u n : E) :
    B u (u-n) = (B u u + B (u-n) (u-n) - B n n)/2 := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [hs n u]
  ring

/-- Isotropy removes the fast-fast skew term exactly. -/
theorem v25_skew_chart_phase (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (uf us nf ns : E) (hff : B uf uf = 0) (hfn : B uf nf = 0) :
    B (uf+us) ((uf+us)-(nf+ns)) =
      B uf us - B uf ns + B us ((uf+us)-(nf+ns)) := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [hff, hfn]
  ring

end

/-- A finite shell aggregation step, preserving absolute coefficient mass. -/
theorem v25_shell_pool {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → κ → ℂ) :
    ∑ k, ‖∑ i, a i k‖ ≤ ∑ i, ∑ k, ‖a i k‖ := by
  calc
    _ ≤ ∑ k, ∑ i, ‖a i k‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact norm_sum_le _ _
    _ = _ := Finset.sum_comm

end OpenAI086
