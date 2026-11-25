import Mathlib
import OpenAI086.PaperWeylBallPacking

/-!
V52 formalization of the repeated-translation sample propagation in the
proof of Lemma 4.3, p.17.  A unimodular phase at each step does not change
Fourier-sample magnitude; the accumulated translation errors are bounded
by the number of steps times the one-step error.

The chart-specific translation identity still has to supply the step
recurrence and its error bound.
-/
namespace OpenAI086

/-- Propagate a large initial Fourier sample through M approximate
unimodular translations. -/
theorem v52_iterated_sample_lower_bound
    (F : ℕ → ℂ) (M : ℕ) (δ e : ℝ)
    (hδ : 0 < δ) (he : 0 ≤ e)
    (hinit : 3*δ/4 ≤ ‖F 0‖)
    (hstep : ∀ j < M, ∃ u : ℂ,
      ‖u‖ = 1 ∧ ‖F (j+1)-u*F j‖ ≤ e)
    (hbudget : (M:ℝ)*e ≤ δ/4) :
    ∀ j, j ≤ M → δ/2 ≤ ‖F j‖ := by
  have hacc : ∀ j, j ≤ M → ‖F j‖ ≥ ‖F 0‖-(j:ℝ)*e := by
    intro j
    induction j with
    | zero =>
        intro _
        simp
    | succ j ih =>
        intro hj
        have hjlt : j < M := by omega
        obtain ⟨u, hu, herr⟩ := hstep j hjlt
        have herr' : ‖u*F j-F (j+1)‖ ≤ e := by
          simpa [norm_sub_rev] using herr
        have htri := norm_add_le (u*F j-F (j+1)) (F (j+1))
        rw [sub_add_cancel, norm_mul, hu, one_mul] at htri
        have hrec : ‖F (j+1)‖ ≥ ‖F j‖-e := by linarith
        have hprev := ih (by omega)
        have hcast : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
        rw [hcast]
        linarith
  intro j hj
  have haccj := hacc j hj
  have hjM : (j:ℝ) ≤ (M:ℝ) := by exact_mod_cast hj
  have hbudgetj : (j:ℝ)*e ≤ (M:ℝ)*e :=
    mul_le_mul_of_nonneg_right hjM he
  linarith

/-- The sample propagation lemma discharges the repeated-sample premise
in the Plancherel return obstruction. All remaining Fourier Lipschitz,
ball-volume, and energy estimates are explicit inputs. -/
theorem v52_return_bound_from_iterated_samples
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (F : E → ℂ) (x ω : E) (M : ℕ)
    (D δ ρ v energy e : ℝ)
    (hδ : 0 < δ) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hρ : 2*ρ < 1) (hsmall : D*ρ ≤ δ/6)
    (hLip : ∀ a b, ‖F a-F b‖ ≤ D*dist a b)
    (hinitial : 3*δ/4 ≤ ‖F x‖)
    (hstep : ∀ j < M, ∃ u : ℂ, ‖u‖ = 1 ∧
      ‖F (x-((j+1:ℕ):ℝ) • ω)-u*F (x-(j:ℝ) • ω)‖ ≤ e)
    (hbudget : (M:ℝ)*e ≤ δ/4)
    (hvolume : ∀ j < M,
      v ≤ (μ (Metric.closedBall (x-(j:ℝ) • ω) ρ)).toReal)
    (hconst : ∀ j < M, Integrable
      ((Metric.closedBall (x-(j:ℝ) • ω) ρ).indicator
        (fun _ : E => (δ/3)^2)) μ)
    (hi : Integrable (fun z => ‖F z‖^2) μ)
    (henergy : (∫ z, ‖F z‖^2 ∂μ) ≤ energy)
    (hcontr : energy < (M:ℝ)*((δ/3)^2*v)) :
    ‖ω‖ < 1 := by
  apply v39_return_bound μ F x ω M D δ ρ v energy hδ hD hρ hsmall hLip
    ?_ hvolume hconst hi henergy hcontr
  intro j hj
  let samples : ℕ → ℂ := fun n => F (x-(n:ℝ) • ω)
  have hinit' : 3*δ/4 ≤ ‖samples 0‖ := by simpa [samples] using hinitial
  have hstep' : ∀ n < M, ∃ u : ℂ,
      ‖u‖ = 1 ∧ ‖samples (n+1)-u*samples n‖ ≤ e := by
    intro n hn
    obtain ⟨u, hu, he'⟩ := hstep n hn
    refine ⟨u, hu, ?_⟩
    simpa [samples, Nat.cast_succ] using he'
  have hall := v52_iterated_sample_lower_bound samples M δ e hδ he
    hinit' hstep' hbudget
  exact hall j (Nat.le_of_lt hj)

end OpenAI086
