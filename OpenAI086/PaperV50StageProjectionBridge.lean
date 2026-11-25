import OpenAI086.PaperV43Lemma33
import OpenAI086.PaperV44L2Projection

/-!
V50: actual continuous L² stage projections for the anchor partitions.

The local columns are honest measurable functions with explicit `MemLp`
witnesses. Each generation's global stage space is the finite span of all
(atom,label)-restricted columns in the common Bochner L² space. A one-step
refinement identity in `L²` gives nested stage spaces, hence actual Mathlib
orthogonal projections. Lemma 3.3 is then applied to these concrete global
stage spaces. To identify each global span projection with the paper's
orthogonal direct sum of local atom projections, one must additionally prove
that columns supported on distinct atoms are orthogonal; that support/orthogonality
identification is deliberately not claimed by this module.

The final part proves that consecutive ordered projection products, when
represented in the inherited last-layer columns, differ by the synthesis of
the coefficient difference.  This is the exact algebraic bridge needed to
feed the private-coordinate lower bound into the restart argument.

Still open: derive the one-step AE refinement identity from the paper's
active-anchor/terminal-cut geometry and masks; identify the pointwise
coefficient fields with the paper's `c(u)`; and connect the L² increment to
the child-root pointwise transition estimate.  No such geometric premise is
silently assumed to be proved here.
-/

noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

section ActualStageColumns

variable {Ω H Atom Label : Type*}
variable [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Fintype Atom] [Fintype Label]
variable (μ : Measure Ω)

/-- Actual measurable local columns, indexed by generation, layer, spatial
atom, and local label. -/
abbrev V50ColumnFamily := ℕ → ℕ → Atom → Label → Ω → H

/-- The actual L² representatives of all local columns at one generation
and layer. -/
def v50AnchorStageColumns
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation layer : ℕ) : Atom × Label → Lp H 2 μ :=
  v44L2Columns μ
    (fun p : Atom × Label => columns generation layer p.1 p.2)
    (fun p : Atom × Label => hcolumns generation layer p.1 p.2)

/-- The actual stage subspace in the common continuous L² space. -/
def v50AnchorStageSpan
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation layer : ℕ) : Submodule ℂ (Lp H 2 μ) :=
  v44ColumnSpan (v50AnchorStageColumns μ columns hcolumns generation layer)

/-- The stage subspace has an actual orthogonal projection, since it is
spanned by a finite family of genuine L² columns. -/
instance v50AnchorStageSpan_hasProjection
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation layer : ℕ) :
    (v50AnchorStageSpan μ columns hcolumns generation layer).HasOrthogonalProjection := by
  unfold v50AnchorStageSpan
  infer_instance

/-- The actual continuous-linear orthogonal projection onto a local-column
stage space. -/
noncomputable def v50AnchorStageProjection
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation layer : ℕ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (v50AnchorStageSpan μ columns hcolumns generation layer).starProjection

/-- The constructed stage projection satisfies all integrated normal
equations against the actual local columns. -/
theorem v50_anchor_stage_projection_moment
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation layer : ℕ) (z w : Lp H 2 μ)
    (hw : w ∈ v50AnchorStageSpan μ columns hcolumns generation layer) :
    inner ℂ (v50AnchorStageProjection μ columns hcolumns generation layer z) w =
      inner ℂ z w := by
  exact v44_projection_moment
    (v50AnchorStageColumns μ columns hcolumns generation layer) z w hw

/-- Every actual stage projection has constant coefficients in its finite
local-column family. -/
theorem v50_anchor_stage_projection_representation
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation layer : ℕ) (z : Lp H 2 μ) :
    ∃ c : Atom × Label → ℂ,
      (∑ p, c p • v50AnchorStageColumns μ columns hcolumns generation layer p) =
        v50AnchorStageProjection μ columns hcolumns generation layer z := by
  exact v44_projection_repr
    (v50AnchorStageColumns μ columns hcolumns generation layer) z

/-- The precise one-step inheritance condition: every old local column is
an almost-everywhere finite linear combination of columns on the next
partition. This is the geometric/mask statement still to be discharged
from the manuscript's active-anchor and terminal-cut construction. -/
def V50OneStepRefinement
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label)) : Prop :=
  ∀ generation layer atom label,
    ∃ c : Atom × Label → ℂ,
      ∀ᵐ x ∂μ,
        (∑ p, c p • columns (generation+1) layer p.1 p.2 x) =
          columns generation layer atom label x

/-- The actual L² stage spans are nested when the local columns satisfy the
one-step inherited-mask/refit identity. -/
theorem v50_anchor_stage_span_step
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (hrefine : V50OneStepRefinement μ columns)
    (generation layer : ℕ) :
    v50AnchorStageSpan μ columns hcolumns generation layer ≤
      v50AnchorStageSpan μ columns hcolumns (generation+1) layer := by
  apply v44_l2_span_refinement μ
    (fun p : Atom × Label => columns generation layer p.1 p.2)
    (fun p : Atom × Label => columns (generation+1) layer p.1 p.2)
    (fun p : Atom × Label => hcolumns generation layer p.1 p.2)
    (fun p : Atom × Label => hcolumns (generation+1) layer p.1 p.2)
  intro p
  exact hrefine generation layer p.1 p.2

/-- Nestedness at any two generations follows from the one-step local
refinement identity. -/
theorem v50_anchor_stage_span_mono
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (hrefine : V50OneStepRefinement μ columns)
    (layer generation later : ℕ) (hgen : generation ≤ later) :
    v50AnchorStageSpan μ columns hcolumns generation layer ≤
      v50AnchorStageSpan μ columns hcolumns later layer := by
  induction later with
  | zero =>
      have hEq : generation = 0 := by omega
      subst generation
      exact le_rfl
  | succ later ih =>
      by_cases hprev : generation ≤ later
      · exact le_trans (ih hprev)
          (v50_anchor_stage_span_step μ columns hcolumns hrefine later layer)
      · have hEq : generation = later + 1 := by omega
        subst generation
        exact le_rfl

end ActualStageColumns

section Lemma33Bridge

variable {Ω H Atom Label Row : Type*}
variable [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Fintype Atom] [Fintype Label] [Fintype Row]
variable (μ : Measure Ω)
variable {T m : ℕ}
variable {Y : Row → Type*}
variable [∀ r, NormedAddCommGroup (Y r)]
variable [∀ r, NormedSpace ℂ (Y r)]

/-- The family of actual continuous L² stage spans, indexed by projection
layer and finite anchor generation in the form required by Lemma 3.3. -/
def v50AnchorStageFamily
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ) :
    ℕ → Fin (T+1) → Submodule ℂ (Lp H 2 μ) :=
  fun layer generation =>
    v50AnchorStageSpan μ columns hcolumns generation.val layer

/-- Every member of the stage family has its actual Mathlib orthogonal
projection. -/
instance v50AnchorStageFamily_hasProjection
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (layer : ℕ) (generation : Fin (T+1)) :
    (v50AnchorStageFamily μ columns hcolumns layer generation).HasOrthogonalProjection := by
  unfold v50AnchorStageFamily
  infer_instance

/-- The one-step AE column-refinement identity gives the nestedness
hypothesis for every layer in the exact Hilbert-space Lemma 3.3. -/
theorem v50_anchor_stage_family_nested
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (hrefine : V50OneStepRefinement μ columns)
    (layer : ℕ) (a b : Fin (T+1)) (hab : a ≤ b) :
    v50AnchorStageFamily μ columns hcolumns layer a ≤
      v50AnchorStageFamily μ columns hcolumns layer b := by
  apply v50_anchor_stage_span_mono μ columns hcolumns hrefine layer a.val b.val
  exact Fin.le_iff_val_le_val.mp hab

/-- Lemma 3.3 for the actual continuous L² projections onto the finite
local-column spans. Once the paper's active-anchor/terminal-cut construction
discharges `hrefine`, this supplies both the row-prefix and square-variation
bounds for the concrete stage projection families. -/
theorem v50_anchor_stage_lemma33
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (hrefine : V50OneStepRefinement μ columns)
    (N : Row → Fin (T+1))
    (B : (r : Row) → Lp H 2 μ →L[ℂ] Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2)
    (x : Lp H 2 μ) :
    V43Lemma33Goal m (v50AnchorStageFamily μ columns hcolumns) N B x := by
  exact v43_lemma33 m (v50AnchorStageFamily μ columns hcolumns)
    (by
      intro layer a b hab
      exact v50_anchor_stage_family_nested μ columns hcolumns hrefine layer a b hab)
    N B hrow x

end Lemma33Bridge

section ProductCoefficients

variable {Ω H Atom Label : Type*}
variable [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Fintype Atom] [Fintype Label]
variable (μ : Measure Ω)

/-- The ordered product of the actual stage projections from Lemma 3.3. -/
noncomputable def v50AnchorOrderedProduct {T : ℕ}
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation : Fin (T+1)) (m : ℕ) (z : Lp H 2 μ) : Lp H 2 μ :=
  v19FiniteProduct
    (fun layer n =>
      (v50AnchorStageFamily μ columns hcolumns layer n).starProjection.toLinearMap.toAddMonoidHom)
    generation m z

/-- A nonempty ordered product lands in the last layer's actual local
column span, because its final operation is that layer's orthogonal
projection. -/
theorem v50_anchor_ordered_product_mem_last_layer {T : ℕ}
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation : Fin (T+1)) (m : ℕ) (hm : 0 < m) (z : Lp H 2 μ) :
    v50AnchorOrderedProduct μ columns hcolumns generation m z ∈
      v50AnchorStageSpan μ columns hcolumns generation.val (m-1) := by
  cases m with
  | zero => omega
  | succ k =>
      change (v50AnchorStageFamily μ columns hcolumns k generation).starProjection
        (v19FiniteProduct
          (fun layer n =>
            (v50AnchorStageFamily μ columns hcolumns layer n).starProjection.toLinearMap.toAddMonoidHom)
          generation k z) ∈ _
      exact (v50AnchorStageFamily μ columns hcolumns k generation).starProjection_apply_mem _

/-- The last-layer coefficient vector of a nonempty ordered product is
obtained from the actual finite-span membership, not postulated. -/
theorem v50_anchor_ordered_product_coefficients {T : ℕ}
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (generation : Fin (T+1)) (m : ℕ) (hm : 0 < m) (z : Lp H 2 μ) :
    ∃ c : Atom × Label → ℂ,
      (∑ p, c p • v50AnchorStageColumns μ columns hcolumns generation.val (m-1) p) =
        v50AnchorOrderedProduct μ columns hcolumns generation m z := by
  have hmem := v50_anchor_ordered_product_mem_last_layer
    μ columns hcolumns generation m hm z
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem

end ProductCoefficients

section CoefficientIncrement

variable {Label X : Type*} [Fintype Label]
variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Difference of two constant-coefficient local refits is exactly the
synthesis of the coefficient difference. -/
theorem v50_synthesis_increment
    (Φ : Label → X) (c d : Label → ℂ) :
    (∑ v, c v • Φ v) - (∑ v, d v • Φ v) =
      ∑ v, (c v - d v) • Φ v := by
  rw [Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp [sub_smul]

end CoefficientIncrement

section ProductIncrement

variable {Ω H Atom Label : Type*}
variable [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Fintype Atom] [Fintype Label]
variable (μ : Measure Ω)

/-- The difference between consecutive ordered projection products is the
synthesis of their coefficient difference in the newer inherited local
column family. This is the exact algebraic identification needed before
applying the private-coordinate transition lower bound. -/
theorem v50_anchor_ordered_product_increment_coefficients {T : ℕ}
    (columns : V50ColumnFamily (Ω := Ω) (H := H) (Atom := Atom) (Label := Label))
    (hcolumns : ∀ generation layer atom label,
      MemLp (columns generation layer atom label) 2 μ)
    (hrefine : V50OneStepRefinement μ columns)
    (generation : Fin T) (m : ℕ) (hm : 0 < m) (z : Lp H 2 μ) :
    ∃ c d : Atom × Label → ℂ,
      v50AnchorOrderedProduct μ columns hcolumns generation.succ m z -
        v50AnchorOrderedProduct μ columns hcolumns generation.castSucc m z =
      ∑ p, (c p - d p) •
        v50AnchorStageColumns μ columns hcolumns generation.succ.val (m-1) p := by
  obtain ⟨c, hc⟩ := v50_anchor_ordered_product_coefficients
    μ columns hcolumns generation.succ m hm z
  have hmemOld := v50_anchor_ordered_product_mem_last_layer
    μ columns hcolumns generation.castSucc m hm z
  have hmemNew : v50AnchorOrderedProduct μ columns hcolumns generation.castSucc m z ∈
      v50AnchorStageSpan μ columns hcolumns generation.succ.val (m-1) := by
    have hstep := v50_anchor_stage_span_step μ columns hcolumns hrefine
      generation.val (m-1)
    simpa using hstep hmemOld
  have hmemNew' : v50AnchorOrderedProduct μ columns hcolumns generation.castSucc m z ∈
      v44ColumnSpan
        (v50AnchorStageColumns μ columns hcolumns generation.succ.val (m-1)) := hmemNew
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmemNew'
  refine ⟨c, d, ?_⟩
  calc
    _ = (∑ p, c p • v50AnchorStageColumns μ columns hcolumns generation.succ.val (m-1) p) -
        (∑ p, d p • v50AnchorStageColumns μ columns hcolumns generation.succ.val (m-1) p) := by
          rw [← hc, ← hd]
    _ = _ := v50_synthesis_increment
      (v50AnchorStageColumns μ columns hcolumns generation.succ.val (m-1)) c d

end ProductIncrement

end OpenAI086
