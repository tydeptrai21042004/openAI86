import Mathlib

/-! Lemma 4.9, p.24: the two-step Malcev-coordinate law and right
polynomial differences. This is a component of the continuous inverse
transfer, not a proof of the external Leng–Sah–Sawhney inverse theorem. -/
namespace OpenAI086
section
variable {H Z : Type*} [AddCommGroup H] [Module ℝ H]
  [AddCommGroup Z] [Module ℝ Z]

def v25StepMul (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) (a b : H × Z) : H × Z :=
  (a.1+b.1, a.2+b.2+B a.1 b.1)

def v25StepInv (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) (a : H × Z) : H × Z :=
  (-a.1, -a.2+B a.1 a.1)

theorem v25_step_assoc (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) (a b c : H × Z) :
    v25StepMul B (v25StepMul B a b) c = v25StepMul B a (v25StepMul B b c) := by
  apply Prod.ext <;> simp [v25StepMul, map_add, LinearMap.add_apply] <;> abel

theorem v25_step_inv_right (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) (a : H × Z) :
    v25StepMul B a (v25StepInv B a) = (0,0) := by
  apply Prod.ext <;> simp [v25StepMul, v25StepInv, map_neg] <;> abel

theorem v25_step_inv_left (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) (a : H × Z) :
    v25StepMul B (v25StepInv B a) a = (0,0) := by
  apply Prod.ext <;> simp [v25StepMul, v25StepInv, map_neg, LinearMap.neg_apply] <;> abel

def v25RightDifference (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) (g : ℤ → H × Z) (n : ℤ) : H × Z :=
  v25StepMul B (g (n+1)) (v25StepInv B (g n))

theorem v25_right_difference_formula (B : H →ₗ[ℝ] H →ₗ[ℝ] Z)
    (g : ℤ → H × Z) (n : ℤ) :
    v25RightDifference B g n =
      ((g (n+1)).1-(g n).1, (g (n+1)).2-(g n).2-B ((g (n+1)).1-(g n).1) (g n).1) := by
  apply Prod.ext <;> simp [v25RightDifference, v25StepMul, v25StepInv, sub_eq_add_neg,
    map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply] <;> abel

/-- The constant horizontal increment θ cancels in the second difference. -/
theorem v25_second_right_difference (B : H →ₗ[ℝ] H →ₗ[ℝ] Z)
    (g : ℤ → H × Z) (θ : H) (hθ : ∀ n, (g (n+1)).1-(g n).1 = θ) (n : ℤ) :
    v25RightDifference B (v25RightDifference B g) n =
      (0, (g (n+1+1)).2-(g (n+1)).2-((g (n+1)).2-(g n).2)-B θ θ) := by
  rw [v25_right_difference_formula, v25_right_difference_formula B g (n+1), v25_right_difference_formula B g n]
  simp only [hθ, sub_self, Prod.mk.injEq, map_zero, LinearMap.zero_apply, sub_zero, true_and]
  have h : B θ ((g (n+1)).1-(g n).1) = B θ θ := congrArg (B θ) (hθ n)
  rw [map_sub] at h
  rw [← h]
  abel

end
end OpenAI086
