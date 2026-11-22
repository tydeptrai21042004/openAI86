import OpenAI086.PaperTargets.Models

/-!
# Lemma 8.3 — paper page 68

Source opening: Lemma 8.3 (Height stabilization). For a nonexceptional primary, all but CdmaxRht ∗heights have

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite exceptional-fraction goal; missing stopping geometry.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 8.3.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_8_3_model_goal
    {n : ℕ} (exceptional : Finset (Fin n)) (rho : ℝ) : Prop :=
  finiteExceptionalBudget exceptional rho

end OpenAI086.PaperTargets
