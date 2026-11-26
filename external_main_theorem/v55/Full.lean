import OpenAI086.PaperV41MainGoal
import ReferenceV55Exact

/-! Transfer the external pointwise bound to the original concrete Schwartz
operator by uniqueness of the principal value, then use the local extension
bridge. No new analytic hypothesis is added to either exported target. -/
noncomputable section
namespace OpenAI086.ReferenceV55
open MeasureTheory Filter Topology

theorem schwartz_estimate : V41SchwartzEstimate := by
  obtain ⟨C, hC, hb⟩ := exact_main
  refine ⟨C, hC, ?_⟩
  intro a b c
  let f : Fin 3 → V24Schwartz := ![a,b,c]
  obtain ⟨g, hg, hbound⟩ := hb f
  obtain ⟨g', hg', hae⟩ := v25_actual_realization f
  have heq : g = g' := by
    funext x
    exact tendsto_nhds_unique (hg x) (hg' x)
  rw [heq, eLpNorm_congr_ae hae, ← v24_L1_ofReal_norm] at hbound
  rw [Fin.prod_univ_three, ← v24_L3_ofReal_norm,
    ← v24_L3_ofReal_norm, ← v24_L3_ofReal_norm] at hbound
  have h' : ENNReal.ofReal ‖v25SchwartzOperator (f 0) (f 1) (f 2)‖ ≤
      ENNReal.ofReal (C * ‖v24SchwartzEmbedding (f 0)‖ *
        ‖v24SchwartzEmbedding (f 1)‖ * ‖v24SchwartzEmbedding (f 2)‖) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul hC]
    simpa only [mul_assoc] using hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h'
  simpa [f] using hreal

theorem full_main : V41FullMainGoal :=
  v41_full_main_of_schwartz_estimate schwartz_estimate
end OpenAI086.ReferenceV55

example : OpenAI086.V41FullMainGoal := OpenAI086.ReferenceV55.full_main
#print axioms OpenAI086.ReferenceV55.schwartz_estimate
#print axioms OpenAI086.ReferenceV55.full_main
