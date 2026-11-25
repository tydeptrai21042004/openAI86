import OpenAI086.PaperV44PrivateRefit

/-! The scalar-input clause of Lemma 3.2 on the actual normalized L²
space. Mathlib's inner product is conjugate-linear in its first slot,
so the column is placed in that slot. Proof candidates, not certificates. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

/-- The inner product with a column reads exactly its two coordinates. -/
theorem v45_column_inner {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ) (i : Fin n) (x : Ω)
    (u : V44Value n) :
    inner ℂ (v44PrivateColumn φ a i x) u =
      u.ofLp 0 * star (φ x i) + u.ofLp i.succ * (a i : ℂ) := by
  classical
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [v44PrivateColumn, WithLp.ofLp_toLp, Fin.cases_zero, Fin.cases_succ, RCLike.inner_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The physical coordinate of the scalar embedding is f; all private
coordinates vanish. -/
def v45ScalarValue {n : ℕ} (f : ℂ) : V44Value n :=
  WithLp.toLp 2 (Fin.cases f (fun _ : Fin n => 0))

/-- Exact moment for a scalar input. Integrability of the physical
residual moment is derived from the L² inner products, not assumed. -/
theorem v45_scalar_moment {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → Fin n → ℂ)
    (a : Fin n → ℝ) (hφ : ∀ i, MemLp (v44PrivateColumn φ a i) 2 μ)
    (z : Lp (V44Value n) 2 μ) (f : Ω → ℂ)
    (hz : ∀ᵐ x ∂μ, z x = v45ScalarValue (f x)) :
    ∃ c : Fin n → ℂ,
      (∑ i, c i • v44L2Columns μ (v44PrivateColumn φ a) hφ i) =
        v44Projection (v44L2Columns μ (v44PrivateColumn φ a) hφ) z ∧
      ∀ i, (∫ x, (f x -
          (v44Projection (v44L2Columns μ (v44PrivateColumn φ a) hφ) z x).ofLp 0)
          * star (φ x i) ∂μ) = (a i : ℂ)^2 * c i := by
  let Φ := v44L2Columns μ (v44PrivateColumn φ a) hφ
  let g := v44Projection Φ z
  obtain ⟨c, hc⟩ := v44_projection_repr Φ z
  have hg : (fun x => g x) =ᵐ[μ] (fun x => ∑ j, c j • v44PrivateColumn φ a j x) := by
    change (fun x => v44Projection Φ z x) =ᵐ[μ] _
    rw [← hc]
    exact v44_l2_sum_ae μ _ hφ c
  refine ⟨c, hc, ?_⟩
  intro i
  let r : Ω → ℂ := fun x => inner ℂ (Φ i x) (z x) - inner ℂ (Φ i x) (g x)
  let m : Ω → ℂ := fun x => (f x - (g x).ofLp 0) * star (φ x i)
  let b : ℂ := (a i : ℂ)^2 * c i
  have hi₁ : Integrable (fun x => inner ℂ (Φ i x) (z x)) μ := L2.integrable_inner _ _
  have hi₂ : Integrable (fun x => inner ℂ (Φ i x) (g x)) μ := L2.integrable_inner _ _
  have hr : Integrable r μ := hi₁.sub hi₂
  have hmoment := v44_projection_moment Φ z (Φ i) (Submodule.subset_span (Set.mem_range_self i))
  have hmoment' : inner ℂ (Φ i) z = inner ℂ (Φ i) g := by
    have h := congrArg (starRingEnd ℂ) hmoment.symm
    simpa only [inner_conj_symm] using h
  have hzero : (∫ x, r x ∂μ) = 0 := by
    dsimp only [r]
    rw [integral_sub hi₁ hi₂]
    rw [← L2.inner_def, ← L2.inner_def, hmoment', sub_self]
  have he : m =ᵐ[μ] fun x => r x + b := by
    filter_upwards [hz, hg, MemLp.coeFn_toLp (hφ i)] with x hx hy hcol
    have hp : (g x).ofLp i.succ = (a i : ℂ)*c i := by
      rw [hy, v44_private_synthesis_coords]
      simp [v42Synthesis]
    have hcol' : Φ i x = v44PrivateColumn φ a i x := hcol
    dsimp only [m, r, b]
    rw [hcol', v45_column_inner, v45_column_inner, hp, hx]
    simp only [v45ScalarValue, WithLp.ofLp_toLp, Fin.cases_zero, Fin.cases_succ, zero_mul, add_zero]
    ring
  calc
    (∫ x, m x ∂μ) = ∫ x, (r x + b) ∂μ := integral_congr_ae he
    _ = b := by
      rw [integral_add hr (integrable_const b), hzero, zero_add]
      simp [MeasureTheory.integral_const, Measure.real]

/-- Paper's epsilon formulation on an explicitly embedded scalar input. -/
theorem v45_scalar_moment_epsilon {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → Fin n → ℂ)
    (ε : Fin n → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hφ : ∀ i, MemLp (v44PrivateColumn φ (fun j => Real.sqrt (ε j)) i) 2 μ)
    (f : Ω → ℂ) (hf : MemLp (fun x => (v45ScalarValue (n := n) (f x))) 2 μ) :
    let Φ := v44L2Columns μ (v44PrivateColumn φ (fun j => Real.sqrt (ε j))) hφ
    let z := hf.toLp (fun x => v45ScalarValue (n := n) (f x))
    ∃ c : Fin n → ℂ, (∑ i, c i • Φ i) = v44Projection Φ z ∧
      ∀ i, (∫ x, (f x - (v44Projection Φ z x).ofLp 0)*star (φ x i) ∂μ) =
        (ε i : ℂ)*c i := by
  dsimp only
  obtain ⟨c, hc, hm⟩ := v45_scalar_moment μ φ (fun j => Real.sqrt (ε j)) hφ
    (hf.toLp _) f (MemLp.coeFn_toLp hf)
  refine ⟨c, hc, fun i => ?_⟩
  rw [hm i]
  have hs : ((Real.sqrt (ε i) : ℝ) : ℂ)^2 = (ε i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hε i)
  rw [hs]

end OpenAI086
