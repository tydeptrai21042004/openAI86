import Mathlib

/-! The exact quadratic cancellation used in Lemma 4.5 (pp. 20–21).
The scalar identity is valid over any commutative ring. Chart lifts,
Fourier expansion and Gevrey tail bounds remain to be formalized. -/
namespace OpenAI086

/-- Weighted progression identity with the two moment cancellations. -/
theorem v18_progression_quadratic_separation {R : Type*} [CommRing R]
    (α j : Fin 4 → R) (x t λ : R)
    (h0 : (∑ s : Fin 4, α s) = 0)
    (h1 : (∑ s : Fin 4, α s * j s) = 0) :
    (∑ s : Fin 4, α s * (λ * (x + j s * t)^2)) =
      (∑ s : Fin 4, α s * (j s)^2) * λ * t^2 := by
  have hpoint (s : Fin 4) :
      α s * (λ * (x + j s * t)^2) =
      α s * (λ*x^2) + (α s*j s)*(2*λ*x*t) +
        (α s*(j s)^2)*(λ*t^2) := by ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, h0, h1, zero_mul, zero_add]
  ring

/-- The exact rational coefficients used to eliminate an input slot i
in favor of the two distinct remaining slots a,b. -/
theorem v18_progression_separation_weights (i a b : ℚ) (hab : a ≠ b) :
    1 + (i-b)/(b-a) + (a-i)/(b-a) = 0 ∧
    i + a*((i-b)/(b-a)) + b*((a-i)/(b-a)) = 0 := by
  have h : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  constructor <;> field_simp [h] <;> ring

/-- Direct separation of an ordinary quadratic phase, the dimension-zero
chart case, with no scale-dependent parameters. -/
theorem v18_progression_pure_quadratic (i a b x t λ : ℝ) (hab : a ≠ b) :
    λ*(x+i*t)^2 + (i-b)/(b-a)*λ*(x+a*t)^2 +
      (a-i)/(b-a)*λ*(x+b*t)^2 = λ*(i-a)*(i-b)*t^2 := by
  have h : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp [h] <;> ring

end OpenAI086
