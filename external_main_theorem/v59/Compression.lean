import TrilinearHT.Auto.Sec04ColumnProjections

/-! Lemma 3.4 (printed p.10). The exponent C(m+1) applies to the
whole base C(m+1)^C log(2D). The reference theorem therefore has the
correct dependence. The new argument handles dependent row codomains
and upgrades the paper's a.e. path count to a pointwise bound on half-open
cells. Reference: Joris Roos, pinned snapshot, Apache-2.0. The single
summand embedding follows Sec13_3BesselRowsLinearSideEnergy. -/
namespace OpenAI086.ReferenceV59
open Auto MeasureTheory
open scoped BigOperators Classical

/-- A finite family of half-open intervals cannot exceed an a.e. overlap
bound at an isolated point: a common interval immediately to its right
would violate the same bound on a positive-measure set. -/
theorem ae_halfopen_overlap {V : Type*} [Fintype V]
    (a b : V → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ᵐ y : ℝ ∂volume,
      ((Finset.univ.filter fun v => y ∈ Set.Ico (a v) (b v)).card : ℝ) ≤ D) :
    ∀ y : ℝ, ((Finset.univ.filter fun v => y ∈ Set.Ico (a v) (b v)).card : ℝ) ≤ D := by
  classical
  intro y
  let S := Finset.univ.filter fun v => y ∈ Set.Ico (a v) (b v)
  change (S.card : ℝ) ≤ D
  by_cases hs : S.Nonempty
  · obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image S b hs
    have hyv := (Finset.mem_filter.mp hv).2
    have hpos : y < b v := hyv.2
    by_contra hn
    have hzero : volume (Set.Ico y (b v)) = 0 := by
      apply measure_mono_null _ (ae_iff.mp h)
      intro x hx hxgood
      apply hn
      have hSsub : S ⊆ Finset.univ.filter fun i => x ∈ Set.Ico (a i) (b i) := by
        intro i hi
        have hyi := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨hyi.1.trans hx.1, hx.2.trans_le (hmin i hi)⟩⟩
      have hc : (S.card : ℝ) ≤ ((Finset.univ.filter fun i => x ∈ Set.Ico (a i) (b i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSsub
      exact hc.trans hxgood
    rw [Real.volume_Ico] at hzero
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hpos))) hzero
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.cast_zero]
    exact hD

/-- Convert the a.e. path assumption before constructing reference tree data. -/
theorem ae_dyadic_path_count {V : Type*} [Fintype V]
    (G : RealDyadicGrid) (birth : V → ℤ × ℤ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ᵐ y : ℝ ∂volume,
      ((Finset.univ.filter fun v => y ∈ dyadicGridCell G (birth v).1 (birth v).2).card : ℝ) ≤ D) :
    ∀ y : ℝ, ((Finset.univ.filter fun v =>
      y ∈ dyadicGridCell G (birth v).1 (birth v).2).card : ℝ) ≤ D := by
  exact ae_halfopen_overlap (fun v => dyadicGridLeft G (birth v).1 (birth v).2)
    (fun v => dyadicGridLeft G (birth v).1 (birth v).2 + dyadicGridLength G (birth v).1) D hD h

section Rows
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → Type*)
  [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℂ (Y i)]

/-- Isometric embedding of an individual dependent Hilbert row into their
finite Hilbert direct sum. Adapted from the reference's piLpSingle. -/
noncomputable def rowSingle (i : ι) : Y i →L[ℂ] PiLp 2 Y :=
  LinearMap.mkContinuous ((WithLp.linearEquiv 2 ℂ (∀ i, Y i)).symm.toLinearMap ∘ₗ
    LinearMap.single ℂ Y i) 1 fun v => by
      rw [one_mul]
      exact le_of_eq (PiLp.norm_single 2 Y i v)

theorem norm_rowSingle (i : ι) (v : Y i) : ‖rowSingle Y i v‖ = ‖v‖ :=
  PiLp.norm_single 2 Y i v

variable {V : Type*} [Fintype V]

/-- Assemble a common-codomain row family without increasing the Bessel
constant or losing locality. -/
noncomputable def dependentRows (D : ColumnTreeData V)
    (u : ι → ℤ × ℤ) (hu : ∀ i, u i ∈ D.cells)
    (B : (i : ι) → ColumnL2 V →L[ℂ] Y i)
    (hB : ∀ z, ∑ i, ‖B i z‖^2 ≤ ‖z‖^2)
    (hloc : ∀ i, (B i).comp (columnL2Restriction
      (dyadicGridCell D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable D.grid (u i).1 (u i).2)) = B i) :
    ColumnRowFamily D ι (PiLp 2 Y) where
  decision := u
  decision_mem := hu
  row := fun i => (rowSingle Y i).comp (B i)
  bound := 1
  bound_nonneg := zero_le_one
  square_sum := by
    intro z
    simpa only [ContinuousLinearMap.comp_apply, norm_rowSingle, one_pow, one_mul] using hB z
  input_locality := by
    intro i
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply]
    rw [show B i (columnL2Restriction (dyadicGridCell D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable D.grid (u i).1 (u i).2) z) = B i z from
      DFunLike.congr_fun (hloc i) z]

/-- Lemma 3.4's pure projection bound, including different row spaces.
The constant C=512 has exactly the printed parenthesized form. -/
theorem lemma34_projections (D : ColumnTreeData V)
    (A : ℕ → InheritedColumnMask D) (m : ℕ) (z : ColumnL2 V)
    (u : ι → ℤ × ℤ) (hu : ∀ i, u i ∈ D.cells)
    (B : (i : ι) → ColumnL2 V →L[ℂ] Y i)
    (hB : ∀ w, ∑ i, ‖B i w‖^2 ≤ ‖w‖^2)
    (hloc : ∀ i, (B i).comp (columnL2Restriction
      (dyadicGridCell D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable D.grid (u i).1 (u i).2)) = B i) :
    Real.sqrt (∑ i, ‖B i (cellColumnProduct D A (hu i) m z)‖^2) ≤
      (512 * ((m : ℝ) + 1)^512 * Real.log (2 * D.budget))^(512 * (m + 1)) * ‖z‖ := by
  let R := dependentRows Y D u hu B hB hloc
  have h := columnSpatialCompression D A m z R (by change (1 : ℝ) ≤ 1; exact le_rfl)
  have he : (finiteRowNorm (fun i => R.row i (cellColumnProduct D A (R.decision_mem i) m z)))^2 =
      ∑ i, ‖B i (cellColumnProduct D A (hu i) m z)‖^2 := by
    rw [finiteRowNorm_sq]
    simp only [R, dependentRows, ContinuousLinearMap.comp_apply, norm_rowSingle]
  rw [← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (finiteRowNorm_nonneg _)]
  exact h

/-- The same paper bound for mixtures of projections and complements. -/
theorem lemma34_complements (D : ColumnTreeData V)
    (A : ℕ → InheritedColumnMask D) (θ : ℕ → Bool) (m : ℕ) (z : ColumnL2 V)
    (u : ι → ℤ × ℤ) (hu : ∀ i, u i ∈ D.cells)
    (B : (i : ι) → ColumnL2 V →L[ℂ] Y i)
    (hB : ∀ w, ∑ i, ‖B i w‖^2 ≤ ‖w‖^2)
    (hloc : ∀ i, (B i).comp (columnL2Restriction
      (dyadicGridCell D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable D.grid (u i).1 (u i).2)) = B i) :
    Real.sqrt (∑ i, ‖B i (operatorComplementProduct
      (fun l => cellColumnProjection D (A l) (hu i)) θ m z)‖^2) ≤
      (1024 * ((m : ℝ) + 1)^1024 * Real.log (2 * D.budget))^(1024 * (m + 1)) * ‖z‖ := by
  let R := dependentRows Y D u hu B hB hloc
  have h := columnSpatialCompression_complements D A θ m z R (by change (1 : ℝ) ≤ 1; exact le_rfl)
  have he : (finiteRowNorm (fun i => R.row i (operatorComplementProduct
      (fun l => cellColumnProjection D (A l) (R.decision_mem i)) θ m z)))^2 =
      ∑ i, ‖B i (operatorComplementProduct
        (fun l => cellColumnProjection D (A l) (hu i)) θ m z)‖^2 := by
    rw [finiteRowNorm_sq]
    simp only [R, dependentRows, ContinuousLinearMap.comp_apply, norm_rowSingle]
  rw [← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (finiteRowNorm_nonneg _)]
  exact h
end Rows
end OpenAI086.ReferenceV59
#print axioms OpenAI086.ReferenceV59.ae_halfopen_overlap
#print axioms OpenAI086.ReferenceV59.ae_dyadic_path_count
#print axioms OpenAI086.ReferenceV59.lemma34_projections
#print axioms OpenAI086.ReferenceV59.lemma34_complements
