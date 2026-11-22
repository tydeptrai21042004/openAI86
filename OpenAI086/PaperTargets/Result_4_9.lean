import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.9 — paper page 23

Source opening: Lemma 4.9 (Continuous bounded inverse). For 0 < δ < 1/2, let g be supported on an interval I, with ∥g∥∞≤1 and ∥g∥U(I) ≥δ. There is a bounded atom φ of complexity at most

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite correlation-to-structured-witness model; missing nilsequence/inverse theorem.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.9.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_9_model_goal
    {n : ℕ} (f : Fin n → ℝ)
    (structured : (Fin n → ℝ) → Prop) (delta : ℝ) : Prop :=
  finiteDetectionTarget f 0 0 delta →
    ∃ g : Fin n → ℝ, structured g ∧
      delta ≤ |∑ i : Fin n, f i * g i|

end OpenAI086.PaperTargets
