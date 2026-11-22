import OpenAI086.PaperTargets.Models

/-!
# Theorem 4.7 — paper page 22

Source opening: Theorem 4.7 (Leng–Sah–Sawhney). For a 1-bounded function f : [L] →C with ∥f∥U3[L] ≥δ, there are a degree-two filtered nilmanifold G/Γ, a polynomial sequence g : Z →G adapted to its

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite correlation-to-structured-witness model; missing nilsequence/inverse theorem.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Theorem 4.7.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_7_model_goal
    {n : ℕ} (f : Fin n → ℝ)
    (structured : (Fin n → ℝ) → Prop) (delta : ℝ) : Prop :=
  finiteDetectionTarget f 0 0 delta →
    ∃ g : Fin n → ℝ, structured g ∧
      delta ≤ |∑ i : Fin n, f i * g i|

end OpenAI086.PaperTargets
