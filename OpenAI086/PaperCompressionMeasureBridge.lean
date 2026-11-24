import Mathlib
import OpenAI086.PaperCompressionMoments

/-! Two measure-theoretic pieces of Lemma 3.4: the normalized leaf
Jensen estimate and the restart lower bound from actual squared
increments. Construction of the stopping tree is not asserted. -/
namespace OpenAI086
open MeasureTheory

/-- Jensen's square inequality on each probability-normalized leaf.
This avoids a separate integration Cauchy–Schwarz API. -/
theorem v38_normalized_leaf_jensen {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hi : Integrable f μ) (hs : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  let a := ∫ x, f x ∂μ
  have hnon : 0 ≤ ∫ x, (f x)^2-2*a*f x+a^2 ∂μ := by
    apply integral_nonneg
    intro x
    nlinarith [sq_nonneg (f x-a)]
  rw [integral_add (hs.sub (hi.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub hs (hi.const_mul (2*a)), integral_const_mul] at hnon
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hnon
  change 0 ≤ (∫ x, (f x)^2 ∂μ)-2*a*a+a^2 at hnon
  change a^2 ≤ _
  nlinarith

/-- Restart lower bound: a path sent to a new attempt has T large
increments. The indicator records membership in the union of new roots.
This derives the integrated cost without assuming the scalar cost bound. -/
theorem v38_restart_increment_lower {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] (μ : Measure Ω) (R : Set Ω)
    (T : ℕ) (d : ℕ → Ω → H) (b : ℝ) (hR : MeasurableSet R)
    (hi : ∀ n ∈ Finset.range T, Integrable (fun x => ‖d n x‖^2) μ)
    (hconst : Integrable (R.indicator (fun _ : Ω => b^2)) μ)
    (hlarge : ∀ x ∈ R, ∀ n ∈ Finset.range T, b^2 ≤ ‖d n x‖^2) :
    (T:ℝ)*b^2*(μ R).toReal ≤ ∑ n ∈ Finset.range T, ∫ x, ‖d n x‖^2 ∂μ := by
  have hstep (n : ℕ) (hn : n ∈ Finset.range T) :
      b^2*(μ R).toReal ≤ ∫ x, ‖d n x‖^2 ∂μ := by
    have h := integral_mono hconst (hi n hn) (fun x => by
      by_cases hx : x ∈ R
      · rw [Set.indicator_of_mem hx]
        exact hlarge x hx n hn
      · rw [Set.indicator_of_notMem hx]
        positivity)
    rw [integral_indicator hR, integral_const] at h
    simpa [Measure.real, smul_eq_mul, mul_comm] using h
  calc
    _ = ∑ _n ∈ Finset.range T, b^2*(μ R).toReal := by simp [mul_assoc]
    _ ≤ _ := Finset.sum_le_sum hstep

/-- Combining the derived lower bound with the nested-prefix variation
and the representative pointwise energy caps gives both restart budgets.
The variation estimate V and the input energy caps are explicit. -/
theorem v38_restart_from_variation {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] (μ : Measure Ω) (R : Set Ω)
    (T : ℕ) (d : ℕ → Ω → H) (a D τ G V parentMass energy childEnergy : ℝ)
    (hT : 0 < T) (ha : 0 < a) (hD : 0 < D) (hτ : 0 < τ) (hV : 0 ≤ V)
    (hR : MeasurableSet R)
    (hi : ∀ n ∈ Finset.range T, Integrable (fun x => ‖d n x‖^2) μ)
    (hconst : Integrable (R.indicator (fun _ : Ω => (D⁻¹*τ*a)^2)) μ)
    (hlarge : ∀ x ∈ R, ∀ n ∈ Finset.range T, (D⁻¹*τ*a)^2 ≤ ‖d n x‖^2)
    (hvar : (∑ n ∈ Finset.range T, ∫ x, ‖d n x‖^2 ∂μ) ≤ V*energy)
    (hbounded : energy ≤ G^2*a^2*parentMass)
    (hchild : childEnergy ≤ G^2*a^2*(μ R).toReal) :
    (μ R).toReal ≤ (V*G^2/((T:ℝ)*(D⁻¹*τ)^2))*parentMass ∧
    childEnergy ≤ (V*G^2/((T:ℝ)*(D⁻¹*τ)^2))*energy := by
  have ht : 0 < (T:ℝ) := by exact_mod_cast hT
  have hb : 0 < D⁻¹*τ := mul_pos (inv_pos.mpr hD) hτ
  have hc : 0 < (T:ℝ)*(D⁻¹*τ)^2 := mul_pos ht (sq_pos_of_pos hb)
  have h := (v38_restart_increment_lower μ R T d (D⁻¹*τ*a) hR hi hconst hlarge).trans hvar
  have hstep : ((T:ℝ)*(D⁻¹*τ)^2)*a^2*(μ R).toReal ≤ V*energy := by
    convert h using 1 <;> ring
  exact v20_anchor_restart_budgets (μ R).toReal parentMass energy childEnergy a G
    ((T:ℝ)*(D⁻¹*τ)^2) V hc ha hV hstep hbounded hchild

end OpenAI086
