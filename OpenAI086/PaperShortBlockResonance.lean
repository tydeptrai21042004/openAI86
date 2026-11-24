import Mathlib

/-! Lemma 7.2, p.55: quadratic randomization preserves resonant terms.
These are the exact Fourier-index identities, not the short-block bound. -/
namespace OpenAI086

/-- The two progression frequency constraints imply phase cancellation. -/
theorem v25_quadratic_resonance (m0 m1 m2 m3 : ℝ)
    (h0 : m0+m1+m2+m3 = 0) (h1 : m1+2*m2+3*m3 = 0) :
    -m0^2 + m1^2/3 - m2^2/3 + m3^2 = 0 := by
  have hm0 : m0 = m2+2*m3 := by linarith
  have hm1 : m1 = -2*m2-3*m3 := by linarith
  rw [hm0, hm1]
  ring

/-- A resonance in the fourth moment is one of the two possible pairings. -/
theorem v25_fourth_moment_pairings (a b c d : ℝ)
    (hs : a+b = c+d) (hq : a^2+b^2 = c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hd : d = a+b-c := by linarith
  have hp : (a-c)*(b-c) = 0 := by
    rw [hd] at hq
    nlinarith only [hq]
  rcases mul_eq_zero.mp hp with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- In slow-fast coordinates the same progression identity holds exactly. -/
theorem v25_slow_fast_progression (δ n0 n1 u v j : ℝ) :
    δ*((1-j)*n0+j*n1 + ((1-j)*u+j*v)) =
      (1-j)*(δ*(n0+u)) + j*(δ*(n1+v)) := by ring

end OpenAI086
