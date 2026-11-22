import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.6 — paper page 21

Source opening: Lemma 4.6 (Single-scale separation). Fix a term in (4), without its coefficient, of complexity at most H. Let ζ be a fixed nonnegative smooth function, equal to one on the range of t/r allowed by

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 4-input form bound; missing the multilinear singular-integral estimate.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.6.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_6_model_goal
    {n : ℕ} (kernel : Fin n → ℝ)
    (arguments : Fin 4 → Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteFourLinearTarget kernel arguments budget

end OpenAI086.PaperTargets
