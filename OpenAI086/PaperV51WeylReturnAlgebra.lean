import Mathlib
import OpenAI086.PaperWeylReturns
import OpenAI086.PaperWeylSubspace
import OpenAI086.PaperWeylBallPacking
import OpenAI086.PaperShortBlockResonance

/-!
V51 source-derived algebraic steps for Lemma 4.3 (pp. 16--18) and
Lemma 7.2 (p. 55).  These results close exact linear-algebra identities;
they do not supply the chart-specific analytic return estimates or the
short-block multilinear estimate.
-/
namespace OpenAI086

/-- The two progression constraints have a two-parameter nullspace.
The basis is exactly c_j(h+j h') with c=(-1,3,-3,1). -/
theorem v51_progression_frequency_kernel_coordinates
    (m0 m1 m2 m3 : ℝ)
    (h0 : m0 + m1 + m2 + m3 = 0)
    (h1 : m1 + 2*m2 + 3*m3 = 0) :
    ∃ h h' : ℝ,
      m0 = -h ∧
      m1 = 3*(h+h') ∧
      m2 = -3*(h+2*h') ∧
      m3 = h+3*h' := by
  have hm2 : m2 = -3*m0-2*m1 := by linarith
  have hm3 : m3 = 2*m0+m1 := by linarith
  refine ⟨-m0, m0+m1/3, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · rw [hm2]
    ring
  · rw [hm3]
    ring

/-- The exact quadratic phase in the four-slot randomization is zero
on the progression-frequency nullspace. -/
theorem v51_progression_randomizer_phase_zero
    (γ m0 m1 m2 m3 : ℝ)
    (h0 : m0 + m1 + m2 + m3 = 0)
    (h1 : m1 + 2*m2 + 3*m3 = 0) :
    γ * (-m0^2 + m1^2/3 - m2^2/3 + m3^2) = 0 := by
  rw [v25_quadratic_resonance m0 m1 m2 m3 h0 h1]
  ring

/-- Consequently the combined complex quadratic modulation is exactly
one. This is the phase-invariance identity used before the fourth-moment
calculation in Lemma 7.2. -/
theorem v51_progression_randomizer_exp_one
    (γ m0 m1 m2 m3 : ℝ)
    (h0 : m0 + m1 + m2 + m3 = 0)
    (h1 : m1 + 2*m2 + 3*m3 = 0) :
    Complex.exp (Complex.I *
      ((γ * (-m0^2 + m1^2/3 - m2^2/3 + m3^2) : ℝ) : ℂ)) = 1 := by
  have hz := v51_progression_randomizer_phase_zero γ m0 m1 m2 m3 h0 h1
  have hzc : ((γ * (-m0^2 + m1^2/3 - m2^2/3 + m3^2) : ℝ) : ℂ) = 0 := by
    exact_mod_cast hz
  simp [hzc]

/-- If the skew pairing of short-return generators is integral and its
absolute value is at most 1/4, the generated real span is isotropic.
This isolates the exact integer-obstruction step in Lemma 4.3. -/
theorem v51_short_return_span_isotropic
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (S : Set E)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ z : ℤ, A x y = (z : ℝ))
    (hsmall : ∀ x ∈ S, ∀ y ∈ S, |A x y| ≤ (1/4 : ℝ)) :
    ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S, A x y = 0 := by
  have hgen : ∀ x ∈ S, ∀ y ∈ S, A x y = 0 := by
    intro x hx y hy
    obtain ⟨z, hz⟩ := hint x hx y hy
    have hz0 : z = 0 :=
      v27_integral_skew_zero 0 0 (A x y) z (by rw [hz]; norm_num)
        (by norm_num) (by norm_num) (hsmall x hx y hy)
    rw [hz]
    exact_mod_cast hz0
  exact v39_isotropic_span A S hgen

end OpenAI086
