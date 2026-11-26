import ReferenceV59Compression

/-! The finite-measure averaging clause of Lemma 3.4. The parameter-dependent
masks may vary, but each family is inherited and obeys the same column budget.
Bochner integrability of the weighted row vector is explicit. A complex density
with respect to a finite positive measure also covers signed/complex averages.
This extends the reference-backed dependent-row compression theorem. -/
namespace OpenAI086.ReferenceV64
open Auto MeasureTheory
open scoped BigOperators Classical

variable {Ω ι V : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Fintype V]
variable (Y : ι → Type*) [∀ i, NormedAddCommGroup (Y i)]
  [∀ i, InnerProductSpace ℂ (Y i)] [∀ i, CompleteSpace (Y i)]

/-- Integral triangle inequality in the *dependent* finite Hilbert row sum.
No cardinality factor is incurred, even if the row spaces differ. -/
theorem weighted_row_average (μ : Measure Ω) (w : Ω → ℂ)
    (F : Ω → PiLp 2 Y) (M : ℝ) (hw : Integrable (fun t => ‖w t‖) μ)
    (hF : Integrable (fun t => w t • F t) μ)
    (hbound : ∀ᵐ t ∂μ, ‖F t‖ ≤ M) :
    Real.sqrt (∑ i, ‖∫ t, w t • F t i ∂μ‖ ^ 2) ≤ M * ∫ t, ‖w t‖ ∂μ := by
  let g : Ω → PiLp 2 Y := fun t => w t • F t
  have hi : Integrable g μ := hF
  let v : PiLp 2 Y := ∫ t, g t ∂μ
  have hcoord (i : ι) : (∫ t, w t • F t i ∂μ) = v i := by
    let L : PiLp 2 Y →L[ℂ] Y i := PiLp.proj 2 Y i
    simpa [L, g, v, PiLp.smul_apply] using L.integral_comp_comm hi
  have hn : Real.sqrt (∑ i, ‖∫ t, w t • F t i ∂μ‖ ^ 2) = ‖v‖ := by
    simp_rw [hcoord]
    rw [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hn]
  calc
    ‖v‖ ≤ ∫ t, ‖g t‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, M * ‖w t‖ ∂μ := by
      apply integral_mono_ae hi.norm (hw.const_mul M)
      filter_upwards [hbound] with t ht
      rw [show ‖g t‖ = ‖w t‖ * ‖F t‖ by simp [g, norm_smul], mul_comm M]
      exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = M * ∫ t, ‖w t‖ ∂μ := integral_const_mul _ _

/-- Lemma 3.4, last sentence: average ordered projection/complement
products with one common fixed finite-measure weight. The uniform
compression bound is obtained from the existing analytic theorem,
not assumed as a hypothesis. Pure products are the all-false mask
(or the appropriate all-projection convention of the reference). -/
theorem lemma34_average (D : ColumnTreeData V)
    (A : Ω → ℕ → InheritedColumnMask D) (θ : Ω → ℕ → Bool)
    (m : ℕ) (z : ColumnL2 V)
    (u : ι → ℤ × ℤ) (hu : ∀ i, u i ∈ D.cells)
    (B : (i : ι) → ColumnL2 V →L[ℂ] Y i)
    (hB : ∀ x, ∑ i, ‖B i x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hloc : ∀ i, (B i).comp (columnL2Restriction
      (dyadicGridCell D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable D.grid (u i).1 (u i).2)) = B i)
    (μ : Measure Ω) (w : Ω → ℂ) (hw : Integrable (fun t => ‖w t‖) μ)
    (hF : Integrable (fun t => w t • (WithLp.toLp 2 (fun i =>
      B i (operatorComplementProduct
        (fun l => cellColumnProjection D (A t l) (hu i)) (θ t) m z)) : PiLp 2 Y)) μ) :
    Real.sqrt (∑ i, ‖∫ t, w t • B i (operatorComplementProduct
      (fun l => cellColumnProjection D (A t l) (hu i)) (θ t) m z) ∂μ‖ ^ 2) ≤
      ((1024 * ((m : ℝ) + 1)^1024 * Real.log (2 * D.budget))^(1024 * (m + 1)) * ‖z‖) *
        ∫ t, ‖w t‖ ∂μ := by
  let F : Ω → PiLp 2 Y := fun t => WithLp.toLp 2 (fun i =>
    B i (operatorComplementProduct
      (fun l => cellColumnProjection D (A t l) (hu i)) (θ t) m z))
  apply weighted_row_average Y μ w F _ hw hF
  apply Filter.Eventually.of_forall
  intro t
  have he : ‖F t‖ = Real.sqrt (∑ i, ‖F t i‖ ^ 2) := by
    rw [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [he]
  exact OpenAI086.ReferenceV59.lemma34_complements Y D (A t) (θ t) m z u hu B hB hloc

end OpenAI086.ReferenceV64
#print axioms OpenAI086.ReferenceV64.weighted_row_average
#print axioms OpenAI086.ReferenceV64.lemma34_average
