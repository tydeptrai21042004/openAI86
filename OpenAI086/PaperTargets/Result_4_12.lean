import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.12 — paper page 27

Source opening: Lemma 4.12 (Local detection). Fix q > 2 and C1 ≥1. Suppose that R, h, u, v occupy the four slots in any order and satisfy

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite correlation-to-structured-witness model; missing nilsequence/inverse theorem.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.12.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_12_model_goal
    {n : ℕ} (f : Fin n → ℝ)
    (structured : (Fin n → ℝ) → Prop) (delta : ℝ) : Prop :=
  finiteDetectionTarget f 0 0 delta →
    ∃ g : Fin n → ℝ, structured g ∧
      delta ≤ |∑ i : Fin n, f i * g i|

end OpenAI086.PaperTargets
