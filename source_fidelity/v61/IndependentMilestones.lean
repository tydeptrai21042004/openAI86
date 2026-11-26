import OpenAI086.PaperV56Lemma32
import OpenAI086.PaperV43Packing
import OpenAI086.PaperV43Lemma33
import OpenAI086.PaperHeightFinalWrappers
import OpenAI086.PaperV56ExceptionalBlocks
import OpenAI086.PaperV51Prop89Assembly
import OpenAI086.OuterStopping

/-! V61. Mathlib-only candidates. The corrected scale count below is on
actual rational-height values and enumerates all integer depths. -/
namespace OpenAI086.SourceV61

/-- Corrected Lemma 3.5(2), with an explicit dimension-dependent bandwidth.
The width estimate is substituted into the full finite qualifying set,
and the result is uniform for every positive integral scaling power. -/
theorem corrected_height_count (d B l : ℕ) (ξ : Fin d → ℝ)
    (r α β : ℝ) (hd : 1 ≤ d) (hB : 2 ≤ B) (hr : 0 < r)
    (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    ((v36Qualifying (v34Values d B ξ) r α β l).card : ℝ) ≤
      (d : ℝ) * (8 * ((d : ℝ) + 1)^2 *
        (Real.log (2 * (B : ℝ)) / Real.log 2) +
        (Real.log β - Real.log α) / Real.log 2 + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU : 0 ≤ (Real.log β - Real.log α) / Real.log 2 :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hα hαβ)) hlog2.le
  have hW := v34_width_nonneg d B
  have hwidth := v35_height_width_bound d B hd hB
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have hx : 0 ≤ 2 * v34Width d B + (Real.log β - Real.log α) / Real.log 2 := by
    linarith
  have hdiv : (2 * v34Width d B + (Real.log β - Real.log α) / Real.log 2) / (l : ℝ) ≤
      2 * v34Width d B + (Real.log β - Real.log α) / Real.log 2 := by
    apply (div_le_iff₀ hlpos).mpr
    nlinarith only [mul_nonneg hx (sub_nonneg.mpr hl1)]
  apply (v36_actual_qualifying_count d B l ξ r α β hr hα hαβ hl).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- Scalar absorption step of Lemma 2.4 without introducing an additive
slack: once the stopping argument gives this inequality, the estimate is
uniform in the depth index. This is not the analytic stopping reduction. -/
theorem absorb_uniform (CN : ℕ → ℝ) (K A c : ℝ)
    (hsmall : K*c ≤ 1/2) (hCN : ∀ n, 0 ≤ CN n)
    (h : ∀ n, CN n ≤ K*(A+c*CN n)) :
    ∀ n, CN n ≤ 2*K*A := by
  intro n
  have hmul := mul_le_mul_of_nonneg_right hsmall (hCN n)
  nlinarith only [h n, hmul]

end OpenAI086.SourceV61

#print axioms OpenAI086.SourceV61.corrected_height_count
#print axioms OpenAI086.SourceV61.absorb_uniform
#print axioms OpenAI086.v43_lemma31
#print axioms OpenAI086.v56_lemma32
#print axioms OpenAI086.v43_lemma33
#print axioms OpenAI086.v36_actual_qualifying_count
#print axioms OpenAI086.v56_primary_exceptional_blocks
#print axioms OpenAI086.v51_prop89_event_energy_assembly
