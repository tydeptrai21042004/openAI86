import Mathlib
import OpenAI086.PaperStatement
import OpenAI086.PrincipalValueGoals

/-!
# Theorem 1.1: exact logical transfer from the plus-shift boundedness theorem

Unlike the previous finite/combinatorial components, this theorem concludes
exactly `OpenAI086.Theorem1_1_Goal`, but ONLY FROM EXPLICIT ANALYTIC
HYPOTHESES. In particular it is NOT an unconditional proof of Theorem 1.1.

The remaining tasks are (1) establish a pointwise plus-shift principal-value
and its L¹ norm bound, (2) prove the truncated integral sign bridge, and
(3) check the harmless invariance of the L¹ seminorm under sign.

The signed pointwise limit is transferred by continuity of negation; no
substitution is hidden in a `by simpa` or a new axiom.
-/

noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology

/-- The strong plus-shift theorem required to recover the *exact* PDF goal.
The published `TrilinearHT.trilinear_ht_bound` is a norm bound on a function
created with `limUnder`; pointwise convergence must also be checked. -/
def PlusShiftPointwiseBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : Fin 3 → SchwartzMap ℝ ℂ,
      ∃ Tf : ℝ → ℂ,
        (∀ x : ℝ,
          Tendsto (fun ε : ℝ => plusTruncHilbert (fun i => f i) x ε)
            (𝓝[>] (0 : ℝ)) (𝓝 (Tf x))) ∧
        eLpNorm Tf 1 ≤
          (ENNReal.ofReal C) * ∏ i : Fin 3, eLpNorm (f i) 3

/-- This theorem closes the exact local *logical reduction*: the
unconditional main bound is reduced to a real plus-shift theorem, a
change-of-variables identity, and an elementary norm symmetry.
Its hypotheses are not yet discharged in the independent repository. -/
theorem Theorem1_1_from_plus_shift
    (hplus : PlusShiftPointwiseBound)
    (hsign : ∀ (f : Fin 3 → SchwartzMap ℝ ℂ) (x ε : ℝ),
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
    have hfun :
        (fun ε : ℝ => truncHilbert (fun i => f i) x ε) =
          (fun ε : ℝ => -plusTruncHilbert (fun i => f i) x ε) :=
      funext (hsign f x)
    rw [hfun]
    exact (hconv x).neg
  · rw [hnorm Tf]
    exact hLp

#check OpenAI086.Theorem1_1_from_plus_shift
#print axioms OpenAI086.Theorem1_1_from_plus_shift
end OpenAI086
