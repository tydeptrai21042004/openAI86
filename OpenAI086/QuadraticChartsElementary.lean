import Mathlib

/-!
# OpenAI #086, Definition 4.1 / Lemma 4.2: d=0 polynomial chart calculus

Proved independently for the ordinary real quadratic phase (the d=0 case
of the paper's chart atoms). The full higher-dimensional rational chart
with Gevrey bounds is NOT modeled here.
-/

namespace OpenAI086

/-- The polynomial phase of a zero-dimensional quadratic chart. -/
def ordinaryQuadratic (λ β γ y : ℝ) : ℝ := λ * y ^ 2 + β * y + γ

/-- Translation acts by an explicit change of quadratic coefficients. -/
theorem ordinaryQuadratic_translate (λ β γ a y : ℝ) :
    ordinaryQuadratic λ β γ (y + a) =
      ordinaryQuadratic λ (β + 2 * λ * a)
        (γ + β * a + λ * a ^ 2) y := by
  unfold ordinaryQuadratic
  ring

/-- Affine change of variables preserves the quadratic chart class. -/
theorem ordinaryQuadratic_affine (λ β γ a b y : ℝ) :
    ordinaryQuadratic λ β γ (a * y + b) =
      ordinaryQuadratic (λ * a ^ 2) (2 * λ * a * b + β * a)
        (λ * b ^ 2 + β * b + γ) y := by
  unfold ordinaryQuadratic
  ring

/-- The product of two zero-dimensional phase factors is obtained by
adding their polynomial phase parameters. -/
theorem ordinaryQuadratic_add (λ₁ β₁ γ₁ λ₂ β₂ γ₂ y : ℝ) :
    ordinaryQuadratic λ₁ β₁ γ₁ y + ordinaryQuadratic λ₂ β₂ γ₂ y =
      ordinaryQuadratic (λ₁ + λ₂) (β₁ + β₂) (γ₁ + γ₂) y := by
  unfold ordinaryQuadratic
  ring

/-- Complex exponentials of quadratic phases multiply exactly. -/
theorem ordinaryQuadratic_exp_mul
    (λ₁ β₁ γ₁ λ₂ β₂ γ₂ y : ℝ) :
    Complex.exp (Complex.I * (ordinaryQuadratic λ₁ β₁ γ₁ y : ℂ)) *
      Complex.exp (Complex.I * (ordinaryQuadratic λ₂ β₂ γ₂ y : ℂ)) =
    Complex.exp (Complex.I *
      (ordinaryQuadratic (λ₁ + λ₂) (β₁ + β₂) (γ₁ + γ₂) y : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  rw [← mul_add]
  congr 1
  exact_mod_cast ordinaryQuadratic_add λ₁ β₁ γ₁ λ₂ β₂ γ₂ y

end OpenAI086
