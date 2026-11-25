import OpenAI086.PaperV44RefiningCuts

/-! Continuous moment representatives for a finite disjoint cut. The
projection is constructed from the given square-integrable columns;
locality and orthogonality of different cut atoms are proved below.
The stopping algorithm and quantitative energy bound are separate tasks. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

section Hilbert
variable {X I : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [Fintype I]

/-- Equality of moments against generators implies equality against every
vector of their complex linear span. -/
theorem v45_moments_span (Φ : I → X) (g z : X)
    (h : ∀ i, inner ℂ g (Φ i) = inner ℂ z (Φ i))
    (w : X) (hw : w ∈ v44ColumnSpan Φ) : inner ℂ g w = inner ℂ z w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  rw [← hc, inner_sum, inner_sum]
  simp only [inner_smul_right, h]

/-- Refits are equal when their input moments agree on the refit span. -/
theorem v45_refit_eq_of_moments (Φ : I → X) (g z : X)
    (h : ∀ i, inner ℂ g (Φ i) = inner ℂ z (Φ i)) :
    v44Projection Φ g = v44Projection Φ z := by
  let u := v44Projection Φ g
  let v := v44Projection Φ z
  have hu : u ∈ v44ColumnSpan Φ := (v44ColumnSpan Φ).starProjection_apply_mem g
  have hv : v ∈ v44ColumnSpan Φ := (v44ColumnSpan Φ).starProjection_apply_mem z
  have hw : u-v ∈ v44ColumnSpan Φ := (v44ColumnSpan Φ).sub_mem hu hv
  have hm : inner ℂ u (u-v) = inner ℂ v (u-v) :=
    (v44_projection_moment Φ g (u-v) hw).trans
      ((v45_moments_span Φ g z h (u-v) hw).trans
        (v44_projection_moment Φ z (u-v) hw).symm)
  have h0 : inner ℂ (u-v) (u-v) = 0 := by rw [inner_sub_left, hm, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
end Hilbert

section Cut
variable {Ω H Q I : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [Fintype Q] [Fintype I]

/-- Bochner L² vectors with disjoint a.e. supports are orthogonal. -/
theorem v45_disjoint_L2_inner (μ : Measure Ω) (A B : Set Ω)
    (hd : Disjoint A B) (u v : Lp H 2 μ)
    (hu : ∀ᵐ x ∂μ, x ∉ A → u x = 0)
    (hv : ∀ᵐ x ∂μ, x ∉ B → v x = 0) : inner ℂ u v = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ _x : Ω, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hu, hv] with x hx hy
      by_cases hA : x ∈ A
      · have hB : x ∉ B := fun h => (Set.disjoint_left.mp hd) hA h
        rw [hy hB, inner_zero_right]
      · rw [hx hA, inner_zero_left]
    _ = 0 := integral_zero

/-- The cut columns are genuine L² functions. Absent labels may be
represented by zero columns; no global label-count bound is required. -/
def v45CutColumns (μ : Measure Ω) (φ : Q → I → Ω → H)
    (hφ : ∀ q i, MemLp (φ q i) 2 μ) (q : Q) : I → Lp H 2 μ :=
  v44L2Columns μ (φ q) (hφ q)

/-- The actual moment representative is the sum of the local refits of
z on the individual cut-column spans (each extended by zero). -/
def v45CutRepresentative (μ : Measure Ω) (φ : Q → I → Ω → H)
    (hφ : ∀ q i, MemLp (φ q i) 2 μ) (z : Lp H 2 μ) : Lp H 2 μ :=
  ∑ q, v44Projection (v45CutColumns μ φ hφ q) z

/-- A local projection has the same support as its defining columns. -/
theorem v45_cut_refit_support (μ : Measure Ω) (A : Q → Set Ω)
    (φ : Q → I → Ω → H) (hφ : ∀ q i, MemLp (φ q i) 2 μ)
    (hs : ∀ q i x, x ∉ A q → φ q i x = 0) (z : Lp H 2 μ) (q : Q) :
    ∀ᵐ x ∂μ, x ∉ A q → v44Projection (v45CutColumns μ φ hφ q) z x = 0 := by
  obtain ⟨c, hc⟩ := v44_projection_repr (v45CutColumns μ φ hφ q) z
  have he := v44_l2_sum_ae μ (φ q) (hφ q) c
  change (fun x => (∑ i, c i • v45CutColumns μ φ hφ q i) x) =ᵐ[μ] _ at he
  rw [hc] at he
  filter_upwards [he] with x hx hA
  rw [hx]
  apply Finset.sum_eq_zero
  intro i _
  rw [hs q i x hA, smul_zero]

/-- Each test column has its full-input moment preserved by the cut
representative. Cross-atom cancellation follows from actual disjointness. -/
theorem v45_cut_moment (μ : Measure Ω) (A : Q → Set Ω)
    (φ : Q → I → Ω → H) (hφ : ∀ q i, MemLp (φ q i) 2 μ)
    (hd : ∀ q r, q ≠ r → Disjoint (A q) (A r))
    (hs : ∀ q i x, x ∉ A q → φ q i x = 0)
    (z : Lp H 2 μ) (q : Q) (i : I) :
    inner ℂ (v45CutRepresentative μ φ hφ z) (v45CutColumns μ φ hφ q i) =
      inner ℂ z (v45CutColumns μ φ hφ q i) := by
  classical
  unfold v45CutRepresentative
  rw [sum_inner, Finset.sum_eq_single q]
  · exact v44_projection_moment (v45CutColumns μ φ hφ q) z _
      (Submodule.subset_span (Set.mem_range_self i))
  · intro r _ hr
    apply v45_disjoint_L2_inner μ (A r) (A q) (hd r q hr)
    · exact v45_cut_refit_support μ A φ hφ hs z r
    · filter_upwards [MemLp.coeFn_toLp (hφ q i)] with x hx hA
      change ((hφ q i).toLp (φ q i)) x = 0
      rw [hx, hs q i x hA]
  · simp

/-- The moment representative has the exact global energy identity,
without assuming orthogonality of its local projection outputs. -/
theorem v45_cut_energy (μ : Measure Ω) (A : Q → Set Ω)
    (φ : Q → I → Ω → H) (hφ : ∀ q i, MemLp (φ q i) 2 μ)
    (hd : ∀ q r, q ≠ r → Disjoint (A q) (A r))
    (hs : ∀ q i x, x ∉ A q → φ q i x = 0) (z : Lp H 2 μ) :
    inner ℂ (v45CutRepresentative μ φ hφ z) (v45CutRepresentative μ φ hφ z) =
      inner ℂ z (v45CutRepresentative μ φ hφ z) := by
  let g := v45CutRepresentative μ φ hφ z
  have hq : ∀ q, inner ℂ g (v44Projection (v45CutColumns μ φ hφ q) z) =
      inner ℂ z (v44Projection (v45CutColumns μ φ hφ q) z) := by
    intro q
    apply v45_moments_span (v45CutColumns μ φ hφ q) g z
    · exact v45_cut_moment μ A φ hφ hd hs z q
    · exact (v44ColumnSpan (v45CutColumns μ φ hφ q)).starProjection_apply_mem z
  change inner ℂ g (∑ q, v44Projection (v45CutColumns μ φ hφ q) z) =
    inner ℂ z (∑ q, v44Projection (v45CutColumns μ φ hφ q) z)
  rw [inner_sum, inner_sum]
  exact Finset.sum_congr rfl (fun q _ => hq q)

/-- Coarse inherited columns are sums of their pieces on a finite cut.
The input moment is therefore preserved and the first-layer coarse
projection of g equals that of z, as required on p.10. -/
theorem v45_inherited_cut_refit {K : Type*} [Fintype K]
    (μ : Measure Ω) (A : Q → Set Ω) (S : Set Ω)
    (φ : Q → I → Ω → H) (hφ : ∀ q i, MemLp (φ q i) 2 μ)
    (hd : ∀ q r, q ≠ r → Disjoint (A q) (A r))
    (hs : ∀ q i x, x ∉ A q → φ q i x = 0)
    (hpartition : ∀ x ∈ S, ∃! q, x ∈ A q) (hsub : ∀ q, A q ⊆ S)
    (ψ : K → Ω → H) (hψ : ∀ i, MemLp (S.indicator (ψ i)) 2 μ)
    (inherit : ∀ i q, ∃ j, φ q j = (A q).indicator (ψ i)) (z : Lp H 2 μ) :
    v44Projection (v44L2Columns μ (fun i => S.indicator (ψ i)) hψ)
      (v45CutRepresentative μ φ hφ z) =
    v44Projection (v44L2Columns μ (fun i => S.indicator (ψ i)) hψ) z := by
  classical
  apply v45_refit_eq_of_moments
  intro i
  choose j hj using inherit i
  have hsum : (∑ q, v45CutColumns μ φ hφ q (j q)) =
      v44L2Columns μ (fun i => S.indicator (ψ i)) hψ i := by
    apply Lp.ext
    have ha := v44_l2_sum_ae μ (fun q => φ q (j q)) (fun q => hφ q (j q)) (fun _ => 1)
    filter_upwards [ha, MemLp.coeFn_toLp (hψ i)] with x hx hy
    change (∑ q, (1 : ℂ) • v45CutColumns μ φ hφ q (j q)) x = _ at hx
    simp only [one_smul] at hx
    change (∑ q, v45CutColumns μ φ hφ q (j q)) x = ((hψ i).toLp _) x
    rw [hx, hy]
    simp only [hj]
    exact v44_cut_indicator_sum A S (ψ i) hpartition hsub x
  rw [← hsum, inner_sum, inner_sum]
  exact Finset.sum_congr rfl (fun q _ => v45_cut_moment μ A φ hφ hd hs z q (j q))

end Cut
end OpenAI086
