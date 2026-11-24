import Mathlib
import OpenAI086.HilbertPrefixEnergy

/-! Lemma 3.4, pp. 10–12. Abstract moment-patching and energy closure.
The construction of cut-cell L² projections and maximal-function estimate
are separate obligations, not assumptions hidden in a completeness claim. -/
namespace OpenAI086

/-- Patch local moment equalities on any finite cut partition. The moments
are additive functionals, so this works also for complex-valued moments. -/
theorem v20_patch_moments {Q X F : Type*} [Fintype Q]
    [AddCommMonoid X] [AddCommMonoid F]
    (moment : X →+ F) (g z : Q → X)
    (h : ∀ q, moment (g q) = moment (z q)) :
    moment (∑ q, g q) = moment (∑ q, z q) := by
  classical
  simp only [map_sum, h]

/-- A moment representative obtained by an orthogonal projection satisfies
its energy/pairing identity, without a coordinate expansion. -/
theorem v20_moment_projection_energy {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (P : X →+ X)
    (hs : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v))
    (hi : ∀ x, P (P x) = P x) (z : X) :
    ‖P z‖^2 = inner ℝ z (P z) := by
  calc
    _ = inner ℝ (P z) (P z) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ z (P (P z)) := hs z (P z)
    _ = _ := by rw [hi]

/-- Quadratic absorption used for the sum S of representative energies.
S ≤ A+B√S implies S ≤ 2A+B². No depth or label count enters. -/
theorem v20_moment_energy_absorb (S A B : ℝ) (hS : 0 ≤ S)
    (h : S ≤ A+B*Real.sqrt S) : S ≤ 2*A+B^2 := by
  have hs := Real.sq_sqrt hS
  nlinarith [sq_nonneg (Real.sqrt S-B)]

/-- Paper p.11: after the low/high stopping-root estimates, the moment
representative energy is at most (8 D⁻² + L_D) ‖z‖². Here L_D is a
nonnegative real upper bound for the large-root multiplicity. -/
theorem v20_moment_representative_energy (S D L Z : ℝ)
    (hS : 0 ≤ S)
    (h : S ≤ 4*D⁻¹^2*Z^2 + Real.sqrt L*Z*Real.sqrt S)
    (hL : 0 ≤ L) : S ≤ (8*D⁻¹^2+L)*Z^2 := by
  have h' := v20_moment_energy_absorb S (4*D⁻¹^2*Z^2) (Real.sqrt L*Z) hS h
  calc
    S ≤ 2*(4*D⁻¹^2*Z^2)+(Real.sqrt L*Z)^2 := h'
    _ = (8*D⁻¹^2+L)*Z^2 := by rw [mul_pow, Real.sq_sqrt hL]; ring

/-- The two anchor restart estimates follow from one energy lower bound
and the bounded representative. E = V G² / (T D⁻² τ²) in the paper. -/
theorem v20_anchor_restart_budgets (mass parentMass energy childEnergy a G cost V : ℝ)
    (hc : 0 < cost) (ha : 0 < a) (hV : 0 ≤ V)
    (hstep : cost*a^2*mass ≤ V*energy)
    (hbounded : energy ≤ G^2*a^2*parentMass)
    (hchild : childEnergy ≤ G^2*a^2*mass) :
    mass ≤ (V*G^2/cost)*parentMass ∧ childEnergy ≤ (V*G^2/cost)*energy := by
  have hscale : 0 < cost*a^2 := mul_pos hc (sq_pos_of_pos ha)
  have hmass : cost*a^2*mass ≤ V*(G^2*a^2*parentMass) :=
    hstep.trans (mul_le_mul_of_nonneg_left hbounded hV)
  constructor
  · have h1 : a^2*(cost*mass) ≤ a^2*(V*G^2*parentMass) := by
      convert hmass using 1 <;> ring
    have h2 := (mul_le_mul_left (sq_pos_of_pos ha)).mp h1
    calc
      mass ≤ V*G^2*parentMass/cost := (le_div_iff₀ hc).2 (by simpa [mul_comm] using h2)
      _ = (V*G^2/cost)*parentMass := by ring
  · have h1 : cost*childEnergy ≤ cost*(G^2*a^2*mass) :=
      mul_le_mul_of_nonneg_left hchild hc.le
    have h2 : cost*(G^2*a^2*mass) ≤ G^2*(V*energy) := by
      convert mul_le_mul_of_nonneg_left hstep (sq_nonneg G) using 1 <;> ring
    have h3 := h1.trans h2
    calc
      childEnergy ≤ G^2*(V*energy)/cost := (le_div_iff₀ hc).2 (by simpa [mul_comm] using h3)
      _ = (V*G^2/cost)*energy := by ring

end OpenAI086
