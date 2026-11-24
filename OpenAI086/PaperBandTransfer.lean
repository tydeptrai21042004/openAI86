import Mathlib

/-! Lemma 6.9, Equation (15): exact outgoing-filter transfer, including
terminal complementary bands. The analytic estimate for far bands remains
separate.  `H` is the bilinear form obtained by fixing the other two slots.
The identity uses no commutation or positivity assumptions. -/
namespace OpenAI086
open scoped BigOperators

/-- For arbitrary finite bands and real weights, subtract the two weighted
forms before taking absolute values. -/
theorem v24_weighted_band_transfer {I J E F : Type*} [Fintype I] [Fintype J]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (H : E →ₗ[ℝ] F →ₗ[ℝ] ℂ) (a : I → E) (c : J → F)
    (u : I → ℝ) (v : J → ℝ) :
    H (∑ i, a i) (∑ j, v j • c j) - H (∑ i, u i • a i) (∑ j, c j) =
      ∑ i, ∑ j, (v j-u i) • H (a i) (c j) := by
  classical
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    sub_smul, Finset.sum_sub_distrib]

/-- The paper's weights include zero for the terminal band `P+1`. -/
def v24BandWeight (P : ℕ) (p : Fin (P+1)) : ℝ :=
  ((P : ℝ) - (p.val : ℝ)) / (P : ℝ)

theorem v24_band_weight_difference (P : ℕ) (p q : Fin (P+1)) :
    v24BandWeight P q - v24BandWeight P p =
      ((p.val : ℝ)-(q.val : ℝ))/(P : ℝ) := by
  unfold v24BandWeight
  rw [← sub_div]
  congr 1
  ring

theorem v24_terminal_band_weight (P : ℕ) : v24BandWeight P (Fin.last P) = 0 := by
  simp [v24BandWeight]

/-- Equation (15) in zero-based indexing. -/
theorem v24_outgoing_band_identity {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (P : ℕ)
    (H : E →ₗ[ℝ] F →ₗ[ℝ] ℂ) (a : Fin (P+1) → E) (c : Fin (P+1) → F) :
    H (∑ i, a i) (∑ j, v24BandWeight P j • c j) -
      H (∑ i, v24BandWeight P i • a i) (∑ j, c j) =
        ∑ i, ∑ j, (((i.val : ℝ)-(j.val : ℝ))/(P : ℝ)) • H (a i) (c j) := by
  rw [v24_weighted_band_transfer]
  simp only [v24_band_weight_difference]

end OpenAI086
