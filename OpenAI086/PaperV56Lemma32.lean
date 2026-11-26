import OpenAI086.PaperV45ScalarMoment

/-! Lemma 3.2 on an actual normalized cell. The active labels are numbered
by Fin n; a_i = sqrt(epsilon_i). Measurability and essential bounds of
columns are the source hypotheses. No Gram estimate or normal equation
is assumed. This assembles and extends the independent V42–V45 proofs. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

/-- Norm of one augmented column, with its private coordinate. -/
theorem v56_private_column_norm_sq {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ) (i : Fin n) (x : Ω) :
    ‖v44PrivateColumn φ a i x‖^2 = ‖φ x i‖^2 + (a i)^2 := by
  classical
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Fin.sum_univ_succ]
  simp only [v44PrivateColumn, WithLp.ofLp_toLp, Fin.cases_zero, Fin.cases_succ]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · intro j _ hj
    simp [hj]
  · simp

/-- Membership in actual Bochner L² follows from the paper's essential
column bound and measurability, not from a separate assumed L² estimate. -/
theorem v56_private_column_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → Fin n → ℂ)
    (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D)
    (hm : ∀ i, AEStronglyMeasurable (v44PrivateColumn φ a i) μ)
    (hb : ∀ᵐ x ∂μ, ∀ i, ‖φ x i‖^2 + (a i)^2 ≤ D^2) :
    ∀ i, MemLp (v44PrivateColumn φ a i) 2 μ := by
  intro i
  apply MemLp.of_bound (hm i) D
  filter_upwards [hb] with x hx
  apply (sq_le_sq₀ (norm_nonneg _) hD.le).mp
  rw [v56_private_column_norm_sq]
  exact hx i

/-- All three assertions of the paper's local coefficient lemma: the
pointwise two-sided estimate, uniqueness and the D^5 average estimate
for the orthogonal refit, and the physical-input moment identity.
The scalar input is given by its canonical physical-coordinate embedding. -/
theorem v56_lemma32 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → Fin n → ℂ)
    (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D) (hn : (n : ℝ) ≤ D)
    (ha : ∀ i, 1 / D ≤ a i)
    (hm : ∀ i, AEStronglyMeasurable (v44PrivateColumn φ a i) μ)
    (hb : ∀ᵐ x ∂μ, ∀ i, ‖φ x i‖^2 + (a i)^2 ≤ D^2) :
    let hφ := v56_private_column_memLp μ φ a D hD hm hb
    let Φ := v44L2Columns μ (v44PrivateColumn φ a) hφ
    (∀ c : Fin n → ℂ, ∀ᵐ x ∂μ,
      v42L2Norm c / D ≤ ‖∑ i, c i • v44PrivateColumn φ a i x‖ ∧
      ‖∑ i, c i • v44PrivateColumn φ a i x‖ ≤ D * Real.sqrt D * v42L2Norm c) ∧
    (∀ z : Lp (V44Value n) 2 μ,
      (∃! c : Fin n → ℂ, (∑ i, c i • Φ i) = v44Projection Φ z) ∧
      (∀ᵐ x ∂μ, ‖v44Projection Φ z x‖ ≤ D^5 * (∫ y, ‖z y‖ ∂μ))) ∧
    (∀ (f : Ω → ℂ) (hf : MemLp (fun x => v45ScalarValue (n := n) (f x)) 2 μ),
      let z := hf.toLp (fun x => v45ScalarValue (n := n) (f x))
      ∃ c : Fin n → ℂ, (∑ i, c i • Φ i) = v44Projection Φ z ∧
        ∀ i, (∫ x, (f x - (v44Projection Φ z x).ofLp 0) * star (φ x i) ∂μ) =
          (a i : ℂ)^2 * c i) := by
  dsimp only
  let hφ := v56_private_column_memLp μ φ a D hD hm hb
  have hapos : ∀ i, 0 < a i := fun i => (one_div_pos.mpr hD).trans_le (ha i)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    filter_upwards [hb] with x hx
    obtain ⟨hl, hu⟩ := v44_private_norm_bounds φ a c D hD hn ha x hx
    refine ⟨?_, hu⟩
    apply (sq_le_sq₀ (div_nonneg (v42_l2_nonneg c) hD.le) (norm_nonneg _)).mp
    rw [div_pow]
    exact hl
  · intro z
    refine ⟨v44_private_refit_unique μ φ a (fun i => (hapos i).ne') hφ z, ?_⟩
    have hz : Integrable (fun x => ‖z x‖) μ :=
      ((Lp.memLp z).integrable (by norm_num)).norm
    exact v44_private_projection_bound μ φ a D hD hn ha hb hφ z hz
  · intro f hf
    exact v45_scalar_moment μ φ a hφ (hf.toLp _) f (MemLp.coeFn_toLp hf)

end OpenAI086
