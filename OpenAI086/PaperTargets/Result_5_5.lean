import OpenAI086.FiniteFourSlotIncrementExpansion
import OpenAI086.PaperTargets.Models

/-!
# Lemma 5.5 — paper page 34

Source opening: Lemma 5.5 (The two-earliest-increments expansion). Take the two earliest increment levels u < t in distinct positions i, j, and let a, b be the complementary positions. Define

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 4-input form bound; missing the multilinear singular-integral estimate.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 5.5.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_5_5_model_goal
    {n : ℕ} (kernel : Fin n → ℝ)
    (arguments : Fin 4 → Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteFourLinearTarget kernel arguments budget

end OpenAI086.PaperTargets

/- V7: real but strictly weaker source-related proof components. -/
#check OpenAI086.finite_two_slot_increment_expansion
#check OpenAI086.finite_four_slot_first_change_expansion
