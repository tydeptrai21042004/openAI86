import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.11 — paper page 27

Source opening: Lemma 4.11 (A generalized von Neumann bound with one L2 input). For four distinct slots occupied by R, g, b, c, one has

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 4-input form bound; missing the multilinear singular-integral estimate.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.11.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_11_model_goal
    {n : ℕ} (kernel : Fin n → ℝ)
    (arguments : Fin 4 → Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteFourLinearTarget kernel arguments budget

end OpenAI086.PaperTargets
