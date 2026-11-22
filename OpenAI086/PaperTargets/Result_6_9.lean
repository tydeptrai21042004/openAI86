import OpenAI086.PaperTargets.Models

/-!
# Lemma 6.9 — paper page 50

Source opening: Lemma 6.9 (Outgoing filters and near-band defects). At a use of (14), suppose slots a, b are fixed side states Sa, Sb, chosen independently of the helper catalog. Suppose the other two slots have

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 4-input form bound; missing the multilinear singular-integral estimate.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 6.9.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_6_9_model_goal
    {n : ℕ} (kernel : Fin n → ℝ)
    (arguments : Fin 4 → Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteFourLinearTarget kernel arguments budget

end OpenAI086.PaperTargets
