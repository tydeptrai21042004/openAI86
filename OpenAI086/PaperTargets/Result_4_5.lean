import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.5 — paper page 20

Source opening: Lemma 4.5 (Progression separation). Let φi, φk be bounded atoms of complexity at most H in two distinct slots i, k, and let a, b denote the remaining slots. Their product has an exact absolutely

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 4-input form bound; missing the multilinear singular-integral estimate.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.5.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_5_model_goal
    {n : ℕ} (kernel : Fin n → ℝ)
    (arguments : Fin 4 → Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteFourLinearTarget kernel arguments budget

end OpenAI086.PaperTargets
