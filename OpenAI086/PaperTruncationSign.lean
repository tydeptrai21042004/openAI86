import Mathlib
import OpenAI086.PaperStatement
import OpenAI086.PrincipalValueGoals
import OpenAI086.SignConvention

/-!
# Candidate proof: exact integral sign bridge for Theorem 1.1

This is a NEW ANALYTIC step, not merely the algebraic kernel reversal.
The integration domain `{t | ε < |t|}` is invariant under `t ↦ -t`.
We use negation-invariance of Lebesgue measure and integration of indicators
in order to obtain a precise equality of Bochner integrals.

STATUS: CANDIDATE, NOT KERNEL-VERIFIED HERE. Imported into the development root for verification; not certified until the pinned kernel passes.
No axiom, sorry, admit, or assumption about the desired integral equality.
-/

noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology

private def truncationSet (ε : ℝ) : Set ℝ := {t : ℝ | ε < |t|}

private theorem truncationSet_measurable (ε : ℝ) :
    MeasurableSet (truncationSet ε) := by
  have hm : Measurable (fun t : ℝ => |t|) := measurable_id.abs
  exact measurableSet_Ioi.preimage hm

private theorem truncationSet_neg_iff (ε t : ℝ) :
    (-t ∈ truncationSet ε ↔ t ∈ truncationSet ε) := by
  simp [truncationSet]

/-- An exact change of variables, valid for arbitrary functions: the
integrability and totalized-integral conventions are handled by the
standard Mathlib Bochner integral lemmas, not smuggled in as assumptions. -/
theorem truncated_kernel_integral_sign (f : Fin 3 → ℝ → ℂ)
    (x ε : ℝ) :
    (∫ t in truncationSet ε, kernelMinus f x t) =
      -(∫ t in truncationSet ε, kernelPlus f x t) := by
  let s := truncationSet ε
  have hs : MeasurableSet s := truncationSet_measurable ε
  have hindicator (t : ℝ) :
      s.indicator (kernelMinus f x) (-t) =
        -(s.indicator (kernelPlus f x) t) := by
    by_cases ht : t ∈ s
    · have hneg : -t ∈ s := (truncationSet_neg_iff ε t).2 ht
      simp [Set.indicator_of_mem, ht, hneg, kernel_reversal]
    · have hneg : -t ∉ s := by
        intro hn
        exact ht ((truncationSet_neg_iff ε t).1 hn)
      simp [Set.indicator_of_not_mem, ht, hneg]
  calc
    (∫ t in s, kernelMinus f x t) =
        ∫ t : ℝ, s.indicator (kernelMinus f x) t :=
          (integral_indicator hs).symm
    _ = ∫ t : ℝ, s.indicator (kernelMinus f x) (-t) := by
          symm
          exact integral_neg_eq_self (s.indicator (kernelMinus f x)) volume
    _ = ∫ t : ℝ, -(s.indicator (kernelPlus f x) t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hindicator
    _ = -(∫ t : ℝ, s.indicator (kernelPlus f x) t) := integral_neg
    _ = -(∫ t in s, kernelPlus f x t) := by rw [integral_indicator hs]

/-- The explicit three-factor product is the same as the Fin 3 product
used by the published plus-shift operator. -/
theorem three_factor_prod (g : Fin 3 → ℂ) :
    (∏ i : Fin 3, g i) = g 0 * g 1 * g 2 := by
  simp [Fin.prod_univ_succ, mul_assoc]

/-- The exact sign conversion for the two truncated operators present
in the repository. This is the first analytic bridge toward Theorem 1.1. -/
theorem truncationSignBridge (f : Fin 3 → ℝ → ℂ) (x ε : ℝ) :
    truncHilbert f x ε = -(plusTruncHilbert f x ε) := by
  have hminus : truncHilbert f x ε =
      ∫ t in truncationSet ε, kernelMinus f x t := by
    rfl
  have hplus : plusTruncHilbert f x ε =
      ∫ t in truncationSet ε, kernelPlus f x t := by
    unfold plusTruncHilbert kernelPlus
    apply setIntegral_congr_fun (truncationSet_measurable ε)
    intro t _
    rw [three_factor_prod]
    norm_num
  rw [hminus, hplus]
  exact truncated_kernel_integral_sign f x ε

#print axioms OpenAI086.truncated_kernel_integral_sign
#print axioms OpenAI086.truncationSignBridge
end OpenAI086
