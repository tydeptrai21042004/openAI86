import Mathlib

/-! Lemma 7.3: split the change of a group output into outer-ball
variation and shared-history variation. No commutation is used. -/
namespace OpenAI086

theorem v23_certified_variation_split {X : Type*} [AddCommGroup X]
    (Lr Lt : X →+ X) (br bt : X) :
    Lt bt-Lr br = (Lt br-Lr br)+Lt (bt-br) := by
  rw [map_sub]
  abel

theorem v23_certified_variation_energy {X I : Type*} [NormedAddCommGroup X]
    [Fintype I] (a b : I → X) (A B : ℝ)
    (ha : (∑ i, ‖a i‖^2) ≤ A) (hb : (∑ i, ‖b i‖^2) ≤ B) :
    (∑ i, ‖a i+b i‖^2) ≤ 2*A+2*B := by
  calc
    _ ≤ ∑ i, (2*‖a i‖^2+2*‖b i‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := pow_le_pow_left₀ (norm_nonneg (a i+b i)) (norm_add_le (a i) (b i)) 2
      nlinarith [sq_nonneg (‖a i‖-‖b i‖)]
    _ = 2*(∑ i, ‖a i‖^2)+2*(∑ i, ‖b i‖^2) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith

end OpenAI086
