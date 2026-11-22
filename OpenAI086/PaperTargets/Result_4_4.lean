import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.4 — paper page 18

Source opening: Lemma 4.4 (Chart expansion and uniform tails). Suppose a rational orthogonal splitting satisfies (2), with heights and the indicated sizes at most B. On a fixed box in Rk there is an exact absolutely

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite absolute-tail budget; missing Gevrey/Fourier decay.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.4.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_4_model_goal
    {n : ℕ} (errors : Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteAbsoluteBudget errors budget

end OpenAI086.PaperTargets
