import OpenAI086.PaperTargets.Models

/-!
# Lemma 7.4 — paper page 60

Source opening: Lemma 7.4 (Side stacks). Fix a near offset q −p in Equation (15), a transfer step, and a search path. The two time-dependent side inputs can be written, at their uses, as a sum of at most

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 3-way splitting identity; missing quantitative structured/uniform control.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 7.4.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_7_4_model_goal
    {n : ℕ} (f : Fin n → ℝ) (tolerance : ℝ) : Prop :=
  ∃ structured uniform err : Fin n → ℝ,
    finiteThreeWayDecomposition f structured uniform err tolerance

end OpenAI086.PaperTargets
