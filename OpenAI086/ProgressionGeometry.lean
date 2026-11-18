import Mathlib

/-!
# OpenAI #086, §2: independent geometry of the progression coordinates

The four-coordinate map is `y j = x + j*t`.  These are the exact elementary
algebraic statements needed at the beginning of the local-form argument.
They do NOT establish Lemma 2.1's integral estimate.
-/

namespace OpenAI086

/-- Two distinct progression coordinates determine `(x,t)` algebraically. -/
theorem two_coordinates_inversion (a b x t : ℝ) :
    (b - a) * x = b * (x + a * t) - a * (x + b * t) ∧
    (b - a) * t = (x + b * t) - (x + a * t) := by
  constructor <;> ring

/-- The two-coordinate mapping is injective whenever its slopes differ. -/
theorem two_coordinates_injective
    (a b x t x' t' : ℝ) (hab : a ≠ b)
    (hi : x + a * t = x' + a * t')
    (hj : x + b * t = x' + b * t') :
    x = x' ∧ t = t' := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hprod : (b - a) * (t - t') = 0 := by
    calc
      (b - a) * (t - t') =
          (x + b*t - (x' + b*t')) - (x + a*t - (x' + a*t')) := by ring
      _ = 0 := by rw [hj, hi]; ring
  have ht : t = t' := by
    have hd : t - t' = 0 := (mul_eq_zero.mp hprod).resolve_left hba
    exact sub_eq_zero.mp hd
  constructor
  · rw [ht] at hi
    linarith
  · exact ht

/-- The Jacobian determinant of `(x,t) ↦ (x+a*t,x+b*t)` is `b-a`. -/
theorem progression_jacobian (a b : ℝ) :
    (1 : ℝ) * b - a * 1 = b - a := by ring

/-- The progression at the three shifts in Theorem 1.1. -/
theorem three_shifts (x t : ℝ) :
    (x + 1*t, x + 2*t, x + 3*t) = (x+t, x+2*t, x+3*t) := by simp

end OpenAI086
