import Mathlib
import OpenAI086.ConditionalMainTransfer

/-!
# Independent candidate: only positive truncation parameters are needed

The previously derived logical transfer required the sign identity for
EVERY real epsilon. The principal value of the manuscript takes epsilon
through positive values. This candidate replaces that unnecessarily strong
assumption with equality eventually in `𝓝[>] 0`, and gives a separate lemma
showing how positive-parameter equality implies the eventual identity.

This is NOT imported into the trusted root and must be compiled by Lean.
Neither the upstream theorem nor the continuous integral sign bridge is
assumed proved by this file.
-/

noncomputable section
namespace OpenAI086
open Filter Topology MeasureTheory

/-- Only a right-neighborhood of zero matters for a principal value. -/
theorem tendsto_of_eventual_negative
    (a b : ℝ → ℂ) (z : ℂ)
    (hsgn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε = -b ε)
    (hplus : Tendsto b (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 (-z)) := by
  exact (hplus.neg).congr' hsgn.symm

/-- A positive-epsilon sign identity supplies the eventual equality. -/
theorem positive_sign_implies_eventual
    (a b : ℝ → ℂ)
    (hsgn : ∀ ε : ℝ, 0 < ε → a ε = -b ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε = -b ε := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hsgn ε hε

/-- Candidate logical conclusion is precisely the unchanged PDF goal.
The actual analytic plus-shift bound, pointwise convergence, and continuous
change of variables are still explicit *hypotheses*. -/
theorem Theorem1_1_from_eventual_sign_candidate
    (hplus : PlusShiftPointwiseBound)
    (hsign : ∀ (f : Fin 3 → SchwartzMap ℝ ℂ) (x : ℝ),
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        truncHilbert (fun i => f i) x ε =
          -(plusTruncHilbert (fun i => f i) x ε))
    (hnorm : ∀ g : ℝ → ℂ,
      eLpNorm (fun x => -g x) 1 = eLpNorm g 1) :
    Theorem1_1_Goal := by
  obtain ⟨C, hC, hbound⟩ := hplus
  refine ⟨C, hC, ?_⟩
  intro f
  obtain ⟨Tf, hconv, hLp⟩ := hbound f
  refine ⟨fun x => -Tf x, ?_, ?_⟩
  · intro x
    exact tendsto_of_eventual_negative
      (fun ε => truncHilbert (fun i => f i) x ε)
      (fun ε => plusTruncHilbert (fun i => f i) x ε)
      (Tf x) (hsign f x) (hconv x)
  · rw [hnorm Tf]
    exact hLp

#print axioms OpenAI086.tendsto_of_eventual_negative
#print axioms OpenAI086.Theorem1_1_from_eventual_sign_candidate
end OpenAI086
