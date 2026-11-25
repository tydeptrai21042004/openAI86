import OpenAI086.CompressionRowError
import OpenAI086.PaperV46CompressionAssembly

/-! V49: the exact coefficient-error row estimate on pp.12--13.

For each row, the coefficient vector has squared norm at most
`(tau * a)^2`.  The row operators are Bessel contractions.  Cauchy--Schwarz
in the finite label variable, followed by the row contraction and the
integrated pathwise column-energy budget, gives the paper's
`tau^2 * a^2 * D^3 * |R|` error term without a label-count loss.
-/
namespace OpenAI086
open scoped BigOperators

/-- Coefficient-error rows are bounded by the total column energy. This
is the precise finite Hilbert-space form of the p.12 double-sum argument. -/
theorem v49_anchor_error_rows
    {Row Label X : Type*} [Fintype Row] [Fintype Label]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {Y : Row → Type*} [∀ r, NormedAddCommGroup (Y r)]
      [∀ r, NormedSpace ℂ (Y r)]
    (B : (r : Row) → X →L[ℂ] Y r)
    (column : Label → X) (error : Row → Label → ℂ)
    (τ a D mass : ℝ)
    (hsmall : ∀ r, (∑ v, ‖error r v‖^2) ≤ (τ*a)^2)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2)
    (hcolumn : (∑ v, ‖column v‖^2) ≤ D^3*mass) :
    (∑ r, ‖B r (∑ v, error r v • column v)‖^2) ≤
      τ^2*a^2*D^3*mass := by
  have hbase := v37_complex_row_error B column error (τ*a) hsmall hrow
  calc
    (∑ r, ‖B r (∑ v, error r v • column v)‖^2)
        ≤ (τ*a)^2*(∑ v, ‖column v‖^2) := hbase
    _ ≤ (τ*a)^2*(D^3*mass) :=
      mul_le_mul_of_nonneg_left hcolumn (sq_nonneg (τ*a))
    _ = τ^2*a^2*D^3*mass := by ring

/-- The row-error theorem with the paper's pathwise budget exposed as a
separate premise.  The caller supplies the integrated column estimate
`sum_v ||1_R Phi_v||_2^2 <= D^3 |R|`, obtained from the pointwise
multiplicity bound by Tonelli. -/
theorem v49_anchor_error_rows_of_pathwise_budget
    {Row Label X : Type*} [Fintype Row] [Fintype Label]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {Y : Row → Type*} [∀ r, NormedAddCommGroup (Y r)]
      [∀ r, NormedSpace ℂ (Y r)]
    (B : (r : Row) → X →L[ℂ] Y r)
    (column : Label → X) (error : Row → Label → ℂ)
    (τ a D : ℝ) (rootMass : ℝ)
    (hsmall : ∀ r, (∑ v, ‖error r v‖^2) ≤ (τ*a)^2)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2)
    (hpathwise : (∑ v, ‖column v‖^2) ≤ D^3*rootMass) :
    (∑ r, ‖B r (∑ v, error r v • column v)‖^2) ≤
      τ^2*a^2*D^3*rootMass :=
  v49_anchor_error_rows B column error τ a D rootMass hsmall hrow hpathwise

/-- Combine the anchor and coefficient-error pieces for one size segment
using the two independent attempt budgets. The ownership map is unique,
so no artificial product of row and attempt counts is introduced. -/
theorem v49_segment_anchor_error_assembly
    {Row Attempt : Type*} [Fintype Row] [Fintype Attempt]
    {Y : Row → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (owner : Row → Attempt)
    (anchor error : (r : Row) → Y r)
    (energy mass : Attempt → ℝ)
    (E M U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (henergy : (∑ a, energy a) ≤ 2*E)
    (hmass : (∑ a, mass a) ≤ 2*M)
    (hanchor : ∀ a,
      (∑ r ∈ Finset.univ.filter (fun r => owner r = a), ‖anchor r‖^2)
        ≤ U*energy a)
    (herror : ∀ a,
      (∑ r ∈ Finset.univ.filter (fun r => owner r = a), ‖error r‖^2)
        ≤ V*mass a) :
    (∑ r, ‖anchor r + error r‖^2) ≤ 4*U*E+4*V*M :=
  v46_segment_row_bound owner anchor error energy mass E M U V
    hU hV henergy hmass hanchor herror

end OpenAI086
