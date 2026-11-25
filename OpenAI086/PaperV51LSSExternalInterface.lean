import Mathlib
import OpenAI086.PaperInverseUniformNormalization

/-!
V51 formal interface for Theorem 4.7 (Leng--Sah--Sawhney), pp. 22--23.
The paper explicitly takes this theorem as an external input.  This file
therefore records its witness contract as a parameter, not as a locally
proved theorem or a new axiom.  The abstract `Model` and its predicates are
an interface boundary; they do not construct a Lie group, lattice, or
polynomial orbit.
-/
namespace OpenAI086

/-- Abstract data returned by the external degree-two inverse theorem.
The correlation uses the conjugated test function, as in the source PDF. -/
structure V51LSSWitness (L : ℕ) (f : Fin L → ℂ) (δ : ℝ) where
  Model : Type
  isDegreeTwoFilteredNilmanifold : Prop
  nilmanifold_certificate : isDegreeTwoFilteredNilmanifold
  orbit : Fin L → Model
  isAdaptedDegreeTwoPolynomialOrbit : Prop
  orbit_certificate : isAdaptedDegreeTwoPolynomialOrbit
  F : Model → ℂ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  dimension : ℕ
  complexity : ℝ
  lipschitzNorm : ℝ
  growthConstant : ℝ
  growthPower : ℕ
  growthConstant_nonneg : 0 ≤ growthConstant
  correlation_lower :
    epsilon ≤ ‖(∑ n : Fin L, f n * star (F (orbit n))) / (L : ℂ)‖
  dimension_bound :
    (dimension : ℝ) ≤ growthConstant * (1 + Real.log (1/δ))^growthPower
  complexity_bound :
    complexity ≤ Real.exp (growthConstant * (1 + Real.log (1/δ))^growthPower)
  lipschitz_bound : lipschitzNorm ≤ complexity
  epsilon_inverse_bound : epsilon⁻¹ ≤ complexity

/-- Explicit external-input contract for Theorem 4.7 on the interval
normalization used in this project.  It is intentionally a hypothesis:
Leng--Sah--Sawhney is cited by the manuscript and is not proved there. -/
def V51LSSExternalInput : Prop :=
  ∀ (L : ℕ) [NeZero (16*L)] (f : Fin L → ℂ) (δ : ℝ),
    0 < L → 0 < δ → δ ≤ 1 →
    (∀ n, ‖f n‖ ≤ 1) →
    δ^8 ≤ v27IntervalCubeRatio L f →
    Nonempty (V51LSSWitness L f δ)

/-- Apply the explicit external theorem input.  This theorem proves no
inverse theorem itself; it makes the dependency visible to downstream
continuous-interval arguments. -/
theorem v51_apply_lss_external_input
    (hLSS : V51LSSExternalInput)
    (L : ℕ) [NeZero (16*L)] (f : Fin L → ℂ) (δ : ℝ)
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hU : δ^8 ≤ v27IntervalCubeRatio L f) :
    Nonempty (V51LSSWitness L f δ) :=
  hLSS L f δ hL hδ hδ1 hf hU

end OpenAI086
