import OpenAI086.PaperV48RestartCutoff
import OpenAI086.PaperV48PrivateTransition
import OpenAI086.PaperCompressionMeasureBridge

/-! V48: assemble the private-coordinate transition lower bound, the
nested-prefix variation budget, and the paper's explicit restart cutoff.

This is a conditional bridge: `hvariation` is the variation estimate for
the actual coefficient-synthesis increments, while `hbounded` and `hchild`
are the representative-energy consequences of the D^5 bound. The full
spatial anchor partitions must still prove these hypotheses from the paper's
construction. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

/-- The actual augmented-column increment associated with two consecutive
coefficient vectors. -/
def v48PrivateIncrement {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (amplitude : Fin n → ℝ)
    (c d : ℕ → Ω → Fin n → ℂ) : ℕ → Ω → V44Value n :=
  fun k x =>
    (∑ i, c k x i • v44PrivateColumn φ amplitude i x) -
    (∑ i, d k x i • v44PrivateColumn φ amplitude i x)

/-- Coefficient movement by at least tau*alpha forces a pointwise lower
bound for the actual augmented-column increment. -/
theorem v48_private_increment_large
    {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (amplitude : Fin n → ℝ)
    (c d : ℕ → Ω → Fin n → ℂ) (R : Set Ω)
    (D τ α : ℝ) (T : ℕ)
    (hD : 0 < D) (hn : (n : ℝ) ≤ D)
    (hamp : ∀ i, 1 / D ≤ amplitude i)
    (hcol : ∀ x ∈ R, ∀ i, ‖φ x i‖^2 + (amplitude i)^2 ≤ D^2)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hmove : ∀ x ∈ R, ∀ k ∈ Finset.range T,
      τ * α ≤ v42L2Norm (c k x - d k x)) :
    ∀ x ∈ R, ∀ k ∈ Finset.range T,
      (D⁻¹ * τ * α)^2 ≤ ‖v48PrivateIncrement φ amplitude c d k x‖^2 := by
  intro x hx k hk
  have hlower := v48_private_column_transition_lower
    φ amplitude (c k x) (d k x) D τ α hD hn hamp (hcol x hx)
    hτ hα (hmove x hx k hk) x
  have hleft : 0 ≤ D⁻¹ * τ * α := by positivity
  exact (sq_le_sq₀ hleft (norm_nonneg _)).mpr hlower

/-- The paper's restart estimates become half-contractions once the
variation estimate and the D^5 representative-energy caps are supplied.
The quantitative coefficient is the cutoff proved on pp.11--12. -/
theorem v48_restart_attempt_contract
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
    (μ : Measure Ω) (R : Set Ω) (T : ℕ) (d : ℕ → Ω → H)
    (a D L parentMass energy childEnergy : ℝ) (m : ℕ)
    (hD : 2 ≤ D) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hLbound : L ≤ (2 * D * ((m : ℝ) + 1))^4)
    (hT : (2 * D * ((m : ℝ) + 1))^(v48RestartExponent m) ≤ (T : ℝ))
    (ha : 0 < a) (hparent : 0 ≤ parentMass) (henergy : 0 ≤ energy)
    (hR : MeasurableSet R)
    (hi : ∀ k ∈ Finset.range T,
      Integrable (fun x => ‖d k x‖^2) μ)
    (hconst : Integrable
      (R.indicator (fun _ : Ω => (D⁻¹ * (D⁻¹)^10 * a)^2)) μ)
    (hlarge : ∀ x ∈ R, ∀ k ∈ Finset.range T,
      (D⁻¹ * (D⁻¹)^10 * a)^2 ≤ ‖d k x‖^2)
    (hvariation :
      (∑ k ∈ Finset.range T, ∫ x, ‖d k x‖^2 ∂μ) ≤
        (m : ℝ)^2 * L^(2*(m-1)) * energy)
    (hbounded : energy ≤ (4*D^5)^2 * a^2 * parentMass)
    (hchild : childEnergy ≤ (4*D^5)^2 * a^2 * (μ R).toReal) :
    (μ R).toReal ≤ (1/2) * parentMass ∧
      childEnergy ≤ (1/2) * energy := by
  have hDpos : 0 < D := by linarith
  have hτ : 0 < D⁻¹ ^ 10 := by positivity
  have hV : 0 ≤ (m : ℝ)^2 * L^(2*(m-1)) := by positivity
  have hTposR : 0 < (T : ℝ) := by
    have hpow : 0 < (2 * D * ((m : ℝ)+1))^(v48RestartExponent m) := by
      positivity
    exact lt_of_lt_of_le hpow hT
  have hTpos : 0 < T := by exact_mod_cast hTposR
  have hbridge := v38_restart_from_variation μ R T d a D (D⁻¹^10) (4*D^5)
    ((m : ℝ)^2 * L^(2*(m-1))) parentMass energy childEnergy
    hTpos ha hDpos hτ hV hR hi hconst hlarge hvariation hbounded hchild
  have hfactorEq :
      (m : ℝ)^2 * L^(2*(m-1)) * (4*D^5)^2 /
        ((T : ℝ) * (D⁻¹ * (D⁻¹)^10)^2) =
      16 * D^32 * (m : ℝ)^2 * L^(2*(m-1)) / (T : ℝ) := by
    calc
      _ = (m : ℝ)^2 * L^(2*(m-1)) * 16 * D^10 /
          ((T : ℝ) * (D⁻¹ * (D⁻¹)^10)^2) := by ring
      _ = _ := v48_restart_factor_from_variation D L m T hDpos hTpos
  have hexp : 2*(m-1) ≤ 2*m := by omega
  have hpow : L^(2*(m-1)) ≤ L^(2*m) :=
    pow_le_pow_right₀ (by linarith : 0 ≤ L) hexp
  have hfactorLe :
      (m : ℝ)^2 * L^(2*(m-1)) * (4*D^5)^2 /
        ((T : ℝ) * (D⁻¹ * (D⁻¹)^10)^2) ≤
      v48RestartFactor D L m T := by
    rw [hfactorEq]
    unfold v48RestartFactor
    apply div_le_div_of_nonneg_right _ hTposR.le
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcut := v48_restart_factor_lt_half D L
    (2 * D * ((m : ℝ)+1)) m T hD hm rfl (by linarith) hLbound hT
  have hsmall :
      (m : ℝ)^2 * L^(2*(m-1)) * (4*D^5)^2 /
        ((T : ℝ) * (D⁻¹ * (D⁻¹)^10)^2) < 1/2 :=
    lt_of_le_of_lt hfactorLe hcut
  rcases hbridge with ⟨hmeasure, henergyChild⟩
  constructor
  · exact le_trans hmeasure
      (mul_le_mul_of_nonneg_right hsmall.le hparent)
  · exact le_trans henergyChild
      (mul_le_mul_of_nonneg_right hsmall.le henergy)

/-- Combined restart theorem for actual augmented-column coefficient
increments. Integrability, the nested-prefix variation estimate, and the
D^5 representative caps are explicit inputs; the coefficient-motion
hypothesis is converted here rather than supplied as a pointwise increment
bound. -/
theorem v48_private_restart_attempt_contract
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (R : Set Ω) (T : ℕ)
    (φ : Ω → Fin n → ℂ) (amplitude : Fin n → ℝ)
    (c d : ℕ → Ω → Fin n → ℂ)
    (a D L parentMass energy childEnergy : ℝ) (m : ℕ)
    (hD : 2 ≤ D) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hLbound : L ≤ (2 * D * ((m : ℝ) + 1))^4)
    (hT : (2 * D * ((m : ℝ) + 1))^(v48RestartExponent m) ≤ (T : ℝ))
    (ha : 0 < a) (hparent : 0 ≤ parentMass) (henergy : 0 ≤ energy)
    (hn : (n : ℝ) ≤ D)
    (hamp : ∀ i, 1/D ≤ amplitude i)
    (hcol : ∀ x ∈ R, ∀ i, ‖φ x i‖^2 + (amplitude i)^2 ≤ D^2)
    (hmove : ∀ x ∈ R, ∀ k ∈ Finset.range T,
      D⁻¹^10 * a ≤ v42L2Norm (c k x - d k x))
    (hR : MeasurableSet R)
    (hi : ∀ k ∈ Finset.range T,
      Integrable (fun x => ‖v48PrivateIncrement φ amplitude c d k x‖^2) μ)
    (hconst : Integrable
      (R.indicator (fun _ : Ω => (D⁻¹ * D⁻¹^10 * a)^2)) μ)
    (hvariation :
      (∑ k ∈ Finset.range T,
        ∫ x, ‖v48PrivateIncrement φ amplitude c d k x‖^2 ∂μ) ≤
        (m : ℝ)^2 * L^(2*(m-1)) * energy)
    (hbounded : energy ≤ (4*D^5)^2 * a^2 * parentMass)
    (hchild : childEnergy ≤ (4*D^5)^2 * a^2 * (μ R).toReal) :
    (μ R).toReal ≤ (1/2) * parentMass ∧
      childEnergy ≤ (1/2) * energy := by
  have hlarge := v48_private_increment_large φ amplitude c d R D (D⁻¹^10) a T
    (by linarith) hn hamp hcol (by positivity) (by linarith) hmove
  exact v48_restart_attempt_contract μ R T
    (v48PrivateIncrement φ amplitude c d) a D L parentMass energy childEnergy m
    hD hm hL hLbound hT ha hparent henergy hR hi hconst hlarge hvariation hbounded hchild

end OpenAI086
