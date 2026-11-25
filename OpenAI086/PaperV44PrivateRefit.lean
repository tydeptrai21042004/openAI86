import OpenAI086.PaperV44L2Projection
import OpenAI086.PaperV42PrivateColumns

/-! Actual private-coordinate column synthesis in the complex Euclidean
value space, rather than the sup norm on a raw function type. All equalities
of L² representatives are almost everywhere. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

abbrev V44Value (n : ℕ) := EuclideanSpace ℂ (Fin (n+1))

def v44PrivateColumn {Ω : Type*} {n : ℕ} (φ : Ω → Fin n → ℂ)
    (a : Fin n → ℝ) (i : Fin n) (x : Ω) : V44Value n :=
  WithLp.toLp 2 (Fin.cases (φ x i) (fun j => if j = i then (a i : ℂ) else 0))

/-- Exact coordinate formula for the synthesis, including the private
component of every selected label. -/
theorem v44_private_synthesis_coords {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ) (c : Fin n → ℂ) (x : Ω) :
    (∑ i, c i • v44PrivateColumn φ a i x).ofLp = v42Synthesis (φ x) a c := by
  classical
  funext j
  have hp := map_sum (EuclideanSpace.proj (𝕜 := ℂ) j)
    (fun i : Fin n => c i • v44PrivateColumn φ a i x) Finset.univ
  simp only [map_smul, EuclideanSpace.coe_proj, smul_eq_mul] at hp
  change (∑ i, c i • v44PrivateColumn φ a i x).ofLp j = _
  rw [hp]
  induction j using Fin.cases with
  | zero =>
      simp [v44PrivateColumn, v42Synthesis]
  | succ k =>
      simp [v44PrivateColumn, v42Synthesis, mul_ite, mul_comm]

/-- Pointwise injectivity follows from the actual private coordinates. -/
theorem v44_private_pointwise_injective {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (x : Ω) :
    Function.Injective (fun c : Fin n → ℂ => ∑ i, c i • v44PrivateColumn φ a i x) := by
  intro c d h
  apply v42_synthesis_injective (φ x) a ha
  rw [← v44_private_synthesis_coords φ a c x, ← v44_private_synthesis_coords φ a d x, h]

/-- A pointwise injective synthesis remains injective in actual L² on a
probability space. No bound on the size of the original label set is used. -/
theorem v44_l2_synthesis_injective {Ω H ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : ι → Ω → H) (hφ : ∀ i, MemLp (φ i) 2 μ)
    (hinj : ∀ x, Function.Injective (fun c : ι → ℂ => ∑ i, c i • φ i x)) :
    Function.Injective (fun c : ι → ℂ => ∑ i, c i • v44L2Columns μ φ hφ i) := by
  intro c d h
  have he : ∀ᵐ x ∂μ, (∑ i, c i • φ i x) = ∑ i, d i • φ i x := by
    filter_upwards [v44_l2_sum_ae μ φ hφ c, v44_l2_sum_ae μ φ hφ d] with x hc hd
    change (∑ i, c i • v44L2Columns μ φ hφ i) x = _ at hc
    change (∑ i, d i • v44L2Columns μ φ hφ i) x = _ at hd
    rw [h] at hc
    exact hc.symm.trans hd
  have hcd : ∀ᵐ x ∂μ, c = d := he.mono (fun x hx => hinj x hx)
  simpa only [ae_const] using hcd

/-- The finite span of the actual augmented columns has an orthogonal
projection with unique constant coefficients. The MemLp witnesses are
square-integrability of the columns, not assumptions of projection or
orthogonality. -/
theorem v44_private_refit_unique {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → Fin n → ℂ)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hφ : ∀ i, MemLp (v44PrivateColumn φ a i) 2 μ) (z : Lp (V44Value n) 2 μ) :
    ∃! c : Fin n → ℂ,
      (∑ i, c i • v44L2Columns μ (v44PrivateColumn φ a) hφ i) =
        v44Projection (v44L2Columns μ (v44PrivateColumn φ a) hφ) z := by
  apply v44_projection_unique_coeff
  exact v44_l2_synthesis_injective μ _ hφ (v44_private_pointwise_injective φ a ha)

/-- The original two-sided coefficient inequalities transferred to the
actual Euclidean value space. -/
theorem v44_private_norm_bounds {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ) (c : Fin n → ℂ) (D : ℝ)
    (hD : 0 < D) (hn : (n:ℝ) ≤ D) (ha : ∀ i, 1/D ≤ a i)
    (x : Ω) (hcol : ∀ i, ‖φ x i‖^2 + (a i)^2 ≤ D^2) :
    (v42L2Norm c)^2 / D^2 ≤ ‖∑ i, c i • v44PrivateColumn φ a i x‖^2 ∧
    ‖∑ i, c i • v44PrivateColumn φ a i x‖ ≤ D*Real.sqrt D*v42L2Norm c := by
  have hnorm : ‖∑ i, c i • v44PrivateColumn φ a i x‖ =
      v42L2Norm (v42Synthesis (φ x) a c) := by
    simpa only [EuclideanSpace.norm_eq, v44_private_synthesis_coords, v42L2Norm]
  rw [hnorm]
  exact v42_complex_column_bounds (φ x) a c D hD hn ha hcol

/-- Actual normalized L² projection, with the D^5 estimate derived from
its energy identity and the concrete column bounds. The input norm is
integrable (automatic for L² on a probability space); this technical
hypothesis is explicit pending the general normalized-measure bridge. -/
theorem v44_private_projection_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → Fin n → ℂ)
    (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D) (hn : (n:ℝ) ≤ D)
    (ha : ∀ i, 1/D ≤ a i)
    (hcol : ∀ᵐ x ∂μ, ∀ i, ‖φ x i‖^2+(a i)^2 ≤ D^2)
    (hφ : ∀ i, MemLp (v44PrivateColumn φ a i) 2 μ)
    (z : Lp (V44Value n) 2 μ) (hz : Integrable (fun x => ‖z x‖) μ) :
    ∀ᵐ x ∂μ, ‖v44Projection (v44L2Columns μ (v44PrivateColumn φ a) hφ) z x‖ ≤
      D^5*(∫ y, ‖z y‖ ∂μ) := by
  let Φ := v44L2Columns μ (v44PrivateColumn φ a) hφ
  let g := v44Projection Φ z
  obtain ⟨c, hc⟩ := v44_projection_repr Φ z
  have hre : (fun x => g x) =ᵐ[μ] fun x => ∑ i, c i • v44PrivateColumn φ a i x := by
    change (fun x => v44Projection Φ z x) =ᵐ[μ] _
    rw [← hc]
    exact v44_l2_sum_ae μ _ hφ c
  let b := v42L2Norm c
  let U := D*Real.sqrt D
  let F := ∫ y, ‖z y‖ ∂μ
  let E := ∫ y, ‖g y‖^2 ∂μ
  have hb : 0 ≤ b := v42_l2_nonneg c
  have hU : 0 ≤ U := mul_nonneg hD.le (Real.sqrt_nonneg _)
  have hF : 0 ≤ F := integral_nonneg (fun _ => norm_nonneg _)
  have hbounds : ∀ᵐ x ∂μ, b^2/D^2 ≤ ‖g x‖^2 ∧ ‖g x‖ ≤ U*b := by
    filter_upwards [hre, hcol] with x hx hy
    rw [hx]
    exact v44_private_norm_bounds φ a c D hD hn ha x hy
  have hgi : Integrable (fun x => ‖g x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
  have hgg : Integrable (fun x => inner ℂ (g x) (g x)) μ := by
    first | exact L2.integrable_inner g g | exact L2.integrable_inner ℂ g g | exact?
  have hzg : Integrable (fun x => inner ℂ (z x) (g x)) μ := by
    first | exact L2.integrable_inner z g | exact L2.integrable_inner ℂ z g | exact?
  have hm : (∫ x, inner ℂ (g x) (g x) ∂μ) = ∫ x, inner ℂ (z x) (g x) ∂μ :=
    v44_L2_energy μ _ hφ z
  have hmoment : E = ∫ x, (inner ℂ (z x) (g x)).re ∂μ := by
    calc
      E = ∫ x, (inner ℂ (g x) (g x)).re ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by simp [inner_self_eq_norm_sq_to_K])
      _ = (∫ x, inner ℂ (g x) (g x) ∂μ).re := integral_re hgg
      _ = (∫ x, inner ℂ (z x) (g x) ∂μ).re := congrArg Complex.re hm
      _ = _ := (integral_re hzg).symm
  have hlo : b^2/D^2 ≤ E := by
    have h := integral_mono_ae (integrable_const (b^2/D^2)) hgi (hbounds.mono (fun _ hx => hx.1))
    simpa [E] using h
  have hup : E ≤ U*b*F := by
    rw [hmoment]
    have h := integral_mono_ae hzg.re (hz.const_mul (U*b)) (by
      filter_upwards [hbounds] with x hx
      calc
        (inner ℂ (z x) (g x)).re ≤ ‖inner ℂ (z x) (g x)‖ := Complex.re_le_norm _
        _ ≤ ‖z x‖ * ‖g x‖ := norm_inner_le_norm _ _
        _ ≤ ‖z x‖ * (U*b) := mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _)
        _ = U*b*‖z x‖ := by ring)
    simpa [F, integral_const_mul] using h
  have hcoef : b ≤ D^2*U*F := by
    rcases v38_refit_coefficient b D U F E hb hD hlo hup with h | h
    · exact h
    · rw [h]; exact mul_nonneg (mul_nonneg (sq_nonneg D) hU) hF
  have hU2 : U^2 = D^3 := by
    dsimp [U]; rw [mul_pow, Real.sq_sqrt hD.le]; ring
  filter_upwards [hbounds] with x hx
  change ‖g x‖ ≤ D^5*F
  calc
    _ ≤ U*b := hx.2
    _ ≤ U*(D^2*U*F) := mul_le_mul_of_nonneg_left hcoef hU
    _ = D^2*U^2*F := by ring
    _ = D^5*F := by rw [hU2]; ring

end OpenAI086
