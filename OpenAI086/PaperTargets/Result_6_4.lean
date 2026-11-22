import OpenAI086.FiniteCatalogClosure
import OpenAI086.PaperTargets.Models

/-!
# Lemma 6.4 — paper page 43

Source opening: Lemma 6.4 (Mask inclusion, closure, and separation). The following assertions hold for every allowed pad.

STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.
This is a finite label-count budget; missing full trees and hereditary graph structure.
The actual analytic theorem still needs a faithful formulation and proof.
-/

namespace OpenAI086.PaperTargets

/-- Finite-model proof obligation for Lemma 6.4.
    Its hypotheses and conclusion DO NOT certify the full paper result. -/
def result_6_4_model_goal
    {n : ℕ} (groups : Fin n → Finset ℕ) (budget : ℕ) : Prop :=
  finiteLabelBudget groups budget

end OpenAI086.PaperTargets

/- V7: real but strictly weaker source-related proof components. -/
#check OpenAI086.finite_catalog_iterate_in_closed_set
