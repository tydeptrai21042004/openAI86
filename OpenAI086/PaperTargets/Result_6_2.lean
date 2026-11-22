import OpenAI086.FinitePathTelescoping
import OpenAI086.PaperTargets.Models

/-!
# Lemma 6.2 — paper page 41

Source opening: Lemma 6.2 (Endpoint bounds along a short path). Suppose two tags can be joined, at one scale, by a path of length L ≤poly(P, k). Their difference data satisfy (2) in their own endpoint coordinates,

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite absolute-tail budget; missing Gevrey/Fourier decay.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 6.2.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_6_2_model_goal
    {n : ℕ} (errors : Fin n → ℝ) (budget : ℝ) : Prop :=
  finiteAbsoluteBudget errors budget

end OpenAI086.PaperTargets

/- V7: real but strictly weaker source-related proof components. -/
#check OpenAI086.finite_path_endpoint_bound
