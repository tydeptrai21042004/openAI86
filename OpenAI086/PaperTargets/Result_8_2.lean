import OpenAI086.PaperTargets.Models

/-!
# Lemma 8.2 — paper page 67

Source opening: Lemma 8.2 (Exceptional blocks and the tiny rational space). Each primary is exceptional in at most Cdmax blocks on a path. At a nonexceptional block, let Krat be the rational span of all

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite exceptional-fraction goal; missing stopping geometry.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 8.2.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_8_2_model_goal
    {n : ℕ} (exceptional : Finset (Fin n)) (rho : ℝ) : Prop :=
  finiteExceptionalBudget exceptional rho

end OpenAI086.PaperTargets
