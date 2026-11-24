import OpenAI086.PaperCubeChangesOfVariables
import OpenAI086.PaperTargets.Models

/-!
# Lemma 4.8 — paper page 22

Source opening: Lemma 4.8 (Elementary cube bounds). The quantity ∥· ∥U is a seminorm. The mixed cube form with possibly different functions gω at its eight vertices satisfies

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite 8-vertex product model; missing full U³ seminorm and Cauchy–Schwarz–Gowers.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 4.8.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_4_8_model_goal
    (vertices : Fin 8 → ℝ) (M : ℝ) : Prop :=
  |∏ i : Fin 8, vertices i| ≤ M ^ 8

end OpenAI086.PaperTargets

-- V18: source-related proof component, not a full paper proof.
#check OpenAI086.v18_cube_high_left_inverse
