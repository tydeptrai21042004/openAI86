import OpenAI086.PaperV50StageProjectionBridge
import OpenAI086.PaperV45CutRefit

/-! Sections 3.2–3.4: identify the global L² projection with local refits,
and derive the one-step refinement identity for actual masked columns on
finite spatial partitions. The anchor construction must still instantiate
these partition and inheritance hypotheses. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

variable {Ω H Atom Label : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [Fintype Atom] [Fintype Label]

/-- The global span projection is exactly the direct sum of the local
refits, for disjoint atoms and columns supported on their own atoms. -/
theorem v54_global_projection_eq_local_sum
    (μ : Measure Ω) (A : Atom → Set Ω) (φ : Atom → Label → Ω → H)
    (hφ : ∀ a i, MemLp (φ a i) 2 μ)
    (hd : ∀ a b, a ≠ b → Disjoint (A a) (A b))
    (hs : ∀ a i x, x ∉ A a → φ a i x = 0) (z : Lp H 2 μ) :
    v44Projection (v44L2Columns μ (fun p : Atom × Label => φ p.1 p.2)
      (fun p => hφ p.1 p.2)) z = v45CutRepresentative μ φ hφ z := by
  classical
  let Φ := v44L2Columns μ (fun p : Atom × Label => φ p.1 p.2)
      (fun p => hφ p.1 p.2)
  let g := v45CutRepresentative μ φ hφ z
  have hmem : g ∈ v44ColumnSpan Φ := by
    change (∑ a, v44Projection (v45CutColumns μ φ hφ a) z) ∈ v44ColumnSpan Φ
    apply Submodule.sum_mem
    intro a _
    obtain ⟨c, hc⟩ := v44_projection_repr (v45CutColumns μ φ hφ a) z
    rw [← hc]
    apply Submodule.sum_mem
    intro i _
    exact (v44ColumnSpan Φ).smul_mem (c i)
      (Submodule.subset_span (Set.mem_range_self (a,i)))
  have hm : ∀ p, inner ℂ g (Φ p) = inner ℂ z (Φ p) := by
    intro p
    exact v45_cut_moment μ A φ hφ hd hs z p.1 p.2
  have hproj := v45_refit_eq_of_moments Φ g z hm
  have hg : v44Projection Φ g = g := by
    -- Both vectors lie in the span, with equal moments against it.
    let w := v44Projection Φ g - g
    have hw : w ∈ v44ColumnSpan Φ := (v44ColumnSpan Φ).sub_mem
      ((v44ColumnSpan Φ).starProjection_apply_mem g) hmem
    have hz : inner ℂ w w = 0 := by
      change inner ℂ (v44Projection Φ g - g) w = 0
      rw [inner_sub_left, v44_projection_moment Φ g w hw, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  exact hproj.symm.trans hg

/-- Construct the masked, spatially restricted column family used by the
paper. Unselected labels are zero, not new independent directions. -/
def v54MaskedColumns [DecidableEq Label] (cell : ℕ → Atom → Set Ω)
    (mask : ℕ → ℕ → Atom → Finset Label) (Φ : Label → Ω → H) :
    V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label) :=
  fun n l a i x => if i ∈ mask n l a then (cell n a).indicator (Φ i) x else 0

/-- A genuine parent map and mask inheritance imply the exact pointwise
coarse-column decomposition in the next generation. The coefficient
vector is constructed here, not assumed. -/
theorem v54_masked_column_refinement [DecidableEq Atom] [DecidableEq Label]
    (μ : Measure Ω) (cell : ℕ → Atom → Set Ω)
    (mask : ℕ → ℕ → Atom → Finset Label) (Φ : Label → Ω → H)
    (parent : ℕ → Atom → Atom)
    (hpartition : ∀ n x, ∃! a, x ∈ cell n a)
    (hparent : ∀ n a, cell (n+1) a ⊆ cell n (parent n a))
    (hinherit : ∀ n l a, mask n l (parent n a) ⊆ mask (n+1) l a) :
    V50OneStepRefinement μ (v54MaskedColumns cell mask Φ) := by
  classical
  intro n l a i
  let c : Atom × Label → ℂ := fun p =>
    if i ∈ mask n l a ∧ parent n p.1 = a ∧ p.2 = i then 1 else 0
  refine ⟨c, Filter.Eventually.of_forall ?_⟩
  intro x
  obtain ⟨b,hb,hu⟩ := hpartition (n+1) x
  have hp : x ∈ cell n (parent n b) := hparent n b hb
  obtain ⟨a',ha',hua'⟩ := hpartition n x
  have hiff : x ∈ cell n a ↔ parent n b = a := by
    constructor
    · intro ha
      exact (hua' _ hp).trans (hua' _ ha).symm
    · intro he
      simpa [← he] using hp
  rw [Finset.sum_eq_single (b,i)]
  · by_cases hi : i ∈ mask n l a
    · by_cases he : parent n b = a
      · have hf : i ∈ mask (n+1) l b := hinherit n l b (by simpa [he] using hi)
        simp [c, v54MaskedColumns, hi, he, hf, Set.indicator_of_mem hb,
          Set.indicator_of_mem (hiff.mpr he)]
      · simp [c, v54MaskedColumns, hi, he, Set.indicator_of_notMem (fun ha => he (hiff.mp ha))]
    · simp [c, v54MaskedColumns, hi]
  · intro p _ hpne
    by_cases hcase : i ∈ mask n l a ∧ parent n p.1 = a ∧ p.2 = i
    · have hne : p.1 ≠ b := by
        intro h
        exact hpne (Prod.ext h hcase.2.2)
      have hn : x ∉ cell (n+1) p.1 := fun hx => hne (hu _ hx)
      simp [c, hcase, v54MaskedColumns, hn, Set.indicator_of_notMem]
    · simp [c, hcase]
  · simp

/-- Actual constructed stage projections are nested, without a separately
assumed AE linear-combination identity. -/
theorem v54_masked_stage_span_step [DecidableEq Atom] [DecidableEq Label]
    (μ : Measure Ω) (cell : ℕ → Atom → Set Ω)
    (mask : ℕ → ℕ → Atom → Finset Label) (Φ : Label → Ω → H)
    (parent : ℕ → Atom → Atom)
    (hpartition : ∀ n x, ∃! a, x ∈ cell n a)
    (hparent : ∀ n a, cell (n+1) a ⊆ cell n (parent n a))
    (hinherit : ∀ n l a, mask n l (parent n a) ⊆ mask (n+1) l a)
    (hcol : ∀ n l a i, MemLp (v54MaskedColumns cell mask Φ n l a i) 2 μ)
    (n l : ℕ) :
    v50AnchorStageSpan μ (v54MaskedColumns cell mask Φ) hcol n l ≤
      v50AnchorStageSpan μ (v54MaskedColumns cell mask Φ) hcol (n+1) l :=
  v50_anchor_stage_span_step μ _ hcol
    (v54_masked_column_refinement μ cell mask Φ parent hpartition hparent hinherit) n l

end OpenAI086
