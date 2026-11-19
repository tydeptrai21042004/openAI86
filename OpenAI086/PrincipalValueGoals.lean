import Mathlib
import OpenAI086.PaperStatement

/-!
# OpenAI #086, exact sign convention bridge still to be proved

The paper uses x-t, x-2t, x-3t. The published third-party formalization
uses x+t, x+2t, x+3t. Changing t to -t changes the sign because 1/t is
odd. This file gives a faithful target to be proved, not an axiom or
an incorrectly claimed theorem.
-/

noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology

/-- Plus-shift version matching the operator in the external project. -/
def plusTruncHilbert (f : Fin 3 → ℝ → ℂ) (x ε : ℝ) : ℂ :=
  ∫ t in {t : ℝ | ε < |t|},
    (∏ i : Fin 3, f i (x + ((i.val + 1 : ℕ) : ℝ) * t)) / (t : ℂ)

/-- Pending analytic change-of-variable theorem. Exact sign, common
cutoff, and Schwartz inputs are part of the statement.
No Lean proof is supplied for this proposition. -/
def TruncationSignBridge_Goal : Prop :=
  ∀ (f : Fin 3 → SchwartzMap ℝ ℂ) (x ε : ℝ),
    0 < ε →
      truncHilbert (fun i => f i) x ε =
        -(plusTruncHilbert (fun i => f i) x ε)

/-- The plus-shift principal-value target, separately from the minus
shift `Theorem1_1_Goal` used by the local project. -/
def PlusShiftSchwartzBound_Goal : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : Fin 3 → SchwartzMap ℝ ℂ,
      eLpNorm
          (fun x : ℝ => limUnder (𝓝[>] (0 : ℝ))
            (plusTruncHilbert (fun i => f i) x)) 1 ≤
        (ENNReal.ofReal C) * ∏ i : Fin 3, eLpNorm (f i) 3

end OpenAI086
