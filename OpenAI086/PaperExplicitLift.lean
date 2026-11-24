import Mathlib
import OpenAI086.PaperBoundedLift

/-! The first-match pointwise linear operator in Lemma 8.1, with fixed
correction and private-coordinate multipliers at a point. The Fourier
construction and measurable field of multipliers remain separate. -/
namespace OpenAI086

noncomputable def v23PhysicalLift {I : Type*} [Fintype I]
    (ζ : ℂ) (q : I → ℂ) : (ℂ × (I → ℂ)) →ₗ[ℂ] ℂ where
  toFun f := ζ*f.1+∑ i, f.2 i*q i
  map_add' f g := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    simp only [Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]

noncomputable def v23PrivateLift {I M : Type*}
    (w : I → M → ℂ) : (ℂ × (I → ℂ)) →ₗ[ℂ] (I → M → ℂ) where
  toFun f i m := f.2 i*w i m
  map_add' f g := by ext i m; simp [add_mul]
  map_smul' c f := by ext i m; simp [smul_eq_mul, mul_assoc]

/-- The linear maps act exactly as the augmented mode-coordinate formula. -/
theorem v23_private_lift_energy {I M : Type*} [Fintype I] [Fintype M]
    (f : ℂ × (I → ℂ)) (w : I → M → ℂ)
    (hw : ∀ i, (∑ m, ‖w i m‖^2) ≤ 1) :
    (∑ i, ∑ m, ‖v23PrivateLift w f i m‖^2) ≤ ∑ i, ‖f.2 i‖^2 := by
  simpa [v23PrivateLift, norm_mul] using
    (v22_lift_private_energy (fun i => ‖f.2 i‖) (fun i m => ‖w i m‖) hw)

end OpenAI086
