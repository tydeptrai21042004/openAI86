import OpenAI086.PaperTargets.Models

/-!
# Lemma 6.3 — paper page 42

Source opening: Lemma 6.3 (Color budget and exceptional roots). For sufficiently large starting k, the preceding construction uses at most L colors, with at most d8

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite exceptional-fraction goal; missing stopping geometry.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 6.3.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_6_3_model_goal
    {n : ℕ} (exceptional : Finset (Fin n)) (rho : ℝ) : Prop :=
  finiteExceptionalBudget exceptional rho

end OpenAI086.PaperTargets
