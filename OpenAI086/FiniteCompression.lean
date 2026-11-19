import Mathlib

/-!
# OpenAI #086, §3.4: fixed-anchor special case of row compression

The main Lemma 3.4 allows the projection product to DEPEND ON THE CELL u(ν)
and controls this dependence uniformly in depth using a private-coordinate
budget. Here we verify the basic common-anchor (cell-independent) step.
This is an actual implication in arbitrary normed spaces, not a proof of
full Lemma 3.4.
-/

namespace OpenAI086

/-- A contraction applied *before the same Bessel row* retains the row
square bound. The result is valid without any commutativity assumptions. -/
theorem fixed_anchor_row_contraction
    {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (B : ι → E → F) (T : E → E)
    (hB : ∀ z, (∑ i : ι, ‖B i z‖ ^ 2) ≤ ‖z‖ ^ 2)
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖)
    (z : E) :
    (∑ i : ι, ‖B i (T z)‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have hh := hB (T z)
  have hle := hT z
  have hnonneg : 0 ≤ ‖T z‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖z‖ := norm_nonneg _
  have hsquares : ‖T z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hnonneg hnonneg2)]
  exact hh.trans hsquares

/-- One may also prepend a SECOND independent contraction. -/
theorem two_fixed_anchors_row_contraction
    {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (B : ι → E → F) (T U : E → E)
    (hB : ∀ z, (∑ i : ι, ‖B i z‖ ^ 2) ≤ ‖z‖ ^ 2)
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖)
    (hU : ∀ z, ‖U z‖ ≤ ‖z‖)
    (z : E) :
    (∑ i : ι, ‖B i (T (U z))‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have hTU : ∀ z, ‖T (U z)‖ ≤ ‖z‖ := by
    intro y
    exact (hT (U y)).trans (hU y)
  exact fixed_anchor_row_contraction B (fun y => T (U y)) hB hTU z

end OpenAI086
