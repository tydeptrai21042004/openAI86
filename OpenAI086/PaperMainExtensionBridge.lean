import OpenAI086.PaperStatement
import OpenAI086.PaperBoundedTrilinearExtension

/-! Combined exact main theorem and Banach-space extension interface.
The PV realization and sharp analytic estimate on the Schwartz class are
still required, and are explicit hypotheses. The unchanged original goal
is not weakened to an a.e. convergence statement. -/
noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology

abbrev V24SchwartzOperator := V24Schwartz →ₗ[ℂ] V24Schwartz →ₗ[ℂ] V24Schwartz →ₗ[ℂ] V24L1
abbrev V24BoundedOperator := V24L3 →L[ℂ] (V24L3 →L[ℂ] (V24L3 →L[ℂ] V24L1))

/-- The original pointwise limits must exist at every x; their a.e. class
must coincide with the output of the actual algebraic Schwartz operator. -/
def V24PVRealization (T : V24SchwartzOperator) : Prop :=
  ∀ f : Fin 3 → V24Schwartz, ∃ g : ℝ → ℂ,
    (∀ x, Tendsto (fun ε : ℝ => truncHilbert (fun i => f i) x ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (g x))) ∧
    g =ᵐ[(volume : Measure ℝ)] (fun x => T (f 0) (f 1) (f 2) x)

theorem v24_L1_ofReal_norm (g : V24L1) :
    ENNReal.ofReal ‖g‖ = eLpNorm (fun x => g x) 1 := by
  rw [Lp.norm_def]
  exact ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)

theorem v24_L3_ofReal_norm (f : V24Schwartz) :
    ENNReal.ofReal ‖v24SchwartzEmbedding f‖ = eLpNorm (fun x => f x) 3 := by
  change ENNReal.ofReal ‖f.toLp 3 (volume : Measure ℝ)‖ = _
  rw [SchwartzMap.norm_toLp]
  exact ENNReal.ofReal_toReal (f.eLpNorm_lt_top (p := 3)).ne

/-- Recover the original statement from a pointwise PV realization and
its norm bound, while simultaneously constructing the unique extension. -/
theorem v24_main_and_extension (T : V24SchwartzOperator) (C : ℝ) (hC : 0 ≤ C)
    (hPV : V24PVRealization T)
    (hT : ∀ a b c, ‖T a b c‖ ≤ C * ‖v24SchwartzEmbedding a‖ *
        ‖v24SchwartzEmbedding b‖ * ‖v24SchwartzEmbedding c‖) :
    Theorem1_1_Goal ∧
    (∃! S : V24BoundedOperator,
      (∀ a b c, S (v24SchwartzEmbedding a) (v24SchwartzEmbedding b)
        (v24SchwartzEmbedding c) = T a b c) ∧ ‖S‖ ≤ C) := by
  refine ⟨?_, v24_L3_extension T C hC hT⟩
  refine ⟨C, hC, ?_⟩
  intro f
  obtain ⟨g, hlim, hae⟩ := hPV f
  refine ⟨g, hlim, ?_⟩
  rw [eLpNorm_congr_ae hae, ← v24_L1_ofReal_norm]
  have h := ENNReal.ofReal_le_ofReal (hT (f 0) (f 1) (f 2))
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hC, v24_L3_ofReal_norm, v24_L3_ofReal_norm, v24_L3_ofReal_norm] at h
  simpa [Fin.prod_univ_succ, mul_assoc] using h

end OpenAI086
