import Mathlib

/-! Lemma 4.10 (p.26): the separator contradiction and the closure-error
bookkeeping. The Hahn–Banach separator, inverse theorem, and L1 duality
are not constructed here. -/
namespace OpenAI086

/-- The numerical part of the separator argument. `u` denotes U(h), `n`
 denotes ‖h‖₂. Applying the bounded inverse input to σh is explicit. -/
theorem v26_inverse_separator_contradiction
    (σ κ M n u : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hM : 0 < M)
    (hn : 1 < n) (hu : σ*n^2 ≤ u) (hbudget : 2*σ ≤ M*κ)
    (hinverse : σ^2 < σ*u → ∃ c : ℝ, κ ≤ σ*c ∧ M*c ≤ 1) : False := by
  have hsq : 1 < n^2 := by
    nlinarith [mul_pos (sub_pos.mpr hn) (by linarith : 0 < n+1)]
  have hσu : σ < u := by
    have hh := mul_lt_mul_of_pos_left hsq hσ
    linarith
  obtain ⟨c, hc, hmc⟩ := hinverse (by
    have hh := mul_lt_mul_of_pos_left hσu hσ
    nlinarith)
  have hc1 := mul_le_mul_of_nonneg_left hc hM.le
  have hc2 := mul_le_mul_of_nonneg_left hmc hσ.le
  have hle : M*κ ≤ σ := by nlinarith
  linarith

/-- Move the closure approximation into the L1 error without changing the
structured or uniform summands. The L1 size is expressed by a seminorm. -/
theorem v26_decomposition_closure_error {E : Type*} [AddCommGroup E]
    (L : E → ℝ) (hadd : ∀ x y, L (x+y) ≤ L x+L y)
    (f s u v : E) (τ : ℝ) (hv : L v ≤ τ/2)
    (he : L (f-(s+u+v)) ≤ τ/2) :
    ∃ v' : E, f = s+u+v' ∧ L v' ≤ τ := by
  refine ⟨v+(f-(s+u+v)), ?_, ?_⟩
  · abel
  · exact (hadd _ _).trans (by linarith)

end OpenAI086
