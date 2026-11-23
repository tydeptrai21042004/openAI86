import Mathlib
import OpenAI086.FiniteDyadicWidthGrouping
import OpenAI086.FiniteOrderedProductExpansion

/-!
# V16: unconditional ordered-product expansion over common dyadic widths

For *every* row-dependent choice of truncation depth, the corresponding
ordered product of projection prefixes expands exactly over the common
finite set of dyadic widths.  Widths are fixed globally; block locations
may vary from row to row and from layer to layer.

This is the algebraic part of the missing `hdecomp` in the V15
`ActualDyadicLevelSum` reduction. It does NOT by itself establish that
the width-grouped terms obey the sharp row-Bessel estimate, nor does it
identify the nested width sums with a single Fintype of width tuples.
-/

namespace OpenAI086

/-- A finite nested sum of *ordered* operator products, allowing an
arbitrary finite set of choices in every layer.  The first layer is
applied first; later layers act on its output. -/
def finiteExpandedLinearProductOnWidths {d : ℕ} {Layer : Type*}
    (widths : Finset ℕ) (Q : Layer → ℕ → FiniteRealEnd d) :
    List Layer → FiniteRealEnd d
  | [] => LinearMap.id
  | i :: rest => ∑ w ∈ widths,
      (finiteExpandedLinearProductOnWidths widths Q rest).comp (Q i w)

/-- Arbitrary finite-width distributivity, with no commutativity
assumption and without a conditional `hdecomp` premise. -/
theorem finite_ordered_product_expansion_on_widths {d : ℕ}
    {Layer : Type*}
    (widths : Finset ℕ) (P : Layer → FiniteRealEnd d)
    (Q : Layer → ℕ → FiniteRealEnd d)
    (hsum : ∀ i, P i = ∑ w ∈ widths, Q i w)
    (layers : List Layer) :
    finiteOrderedLinearProduct P layers =
      finiteExpandedLinearProductOnWidths widths Q layers := by
  classical
  induction layers with
  | nil => rfl
  | cons i rest ih =>
      apply LinearMap.ext
      intro x
      change (finiteOrderedLinearProduct P rest) (P i x) =
        (∑ w ∈ widths,
          (finiteExpandedLinearProductOnWidths widths Q rest).comp (Q i w)) x
      rw [ih, hsum i]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      exact map_sum (finiteExpandedLinearProductOnWidths widths Q rest)
        (fun w => (Q i w) x) widths

/-- This replaces the former single-layer `hlevels` assumption: each
selected prefix actually expands into the *same* set of possible
widths, even though every layer may have a different truncation depth.
The statement is an equality of ordered linear operators. -/
theorem finite_ordered_actual_prefix_width_expansion {d : ℕ}
    {Layer : Type*}
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Layer → ℕ) (k : ℕ)
    (hN : ∀ i, N i + 1 ≤ 2 ^ k)
    (layers : List Layer) :
    finiteOrderedLinearProduct (fun i => P i (N i)) layers =
      finiteExpandedLinearProductOnWidths (finiteDyadicWidthSet k)
        (fun i w => finiteLinearWidthLevel (P i) k 0 (N i + 1) w)
        layers := by
  apply finite_ordered_product_expansion_on_widths
    (finiteDyadicWidthSet k)
    (fun i => P i (N i))
    (fun i w => finiteLinearWidthLevel (P i) k 0 (N i + 1) w)
  intro i
  exact (finite_linear_prefix_grouped_by_width (P i) k (N i) (hN i)).symm

/-- A stronger row-dependent specialization: no common prefix depth is
needed, and different rows need not have the same dyadic block lists.
This is the precise algebraic part of manuscript Lemma 3.3. -/
theorem finite_row_actual_prefix_width_expansion {d : ℕ}
    {Row Layer : Type*}
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Row → Layer → ℕ) (k : ℕ)
    (hN : ∀ r i, N r i + 1 ≤ 2 ^ k)
    (layers : List Layer) (r : Row) :
    finiteOrderedLinearProduct (fun i => P i (N r i)) layers =
      finiteExpandedLinearProductOnWidths (finiteDyadicWidthSet k)
        (fun i w => finiteLinearWidthLevel (P i) k 0 (N r i + 1) w)
        layers := by
  exact finite_ordered_actual_prefix_width_expansion P (N r) k
    (hN r) layers

/-- Applying a genuinely linear row functional preserves the exact
row-specific expansion. This rules out nonlinear fake-row premises. -/
theorem finite_linear_row_actual_prefix_width_expansion {d : ℕ}
    {Row Layer : Type*}
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Row → Layer → ℕ) (k : ℕ)
    (hN : ∀ r i, N r i + 1 ≤ 2 ^ k)
    (layers : List Layer)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (r : Row) (x : Fin d → ℝ) :
    B r ((finiteOrderedLinearProduct (fun i => P i (N r i)) layers) x) =
      B r ((finiteExpandedLinearProductOnWidths (finiteDyadicWidthSet k)
        (fun i w => finiteLinearWidthLevel (P i) k 0 (N r i + 1) w)
        layers) x) := by
  rw [finite_row_actual_prefix_width_expansion P N k hN layers r]

end OpenAI086
