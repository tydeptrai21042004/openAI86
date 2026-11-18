import Mathlib

/-!
Targeted audits of three proof-text issues in OpenAI #086.
These are deliberately LIMITED model theorems/counterexamples.
They neither refute nor prove Theorem 1.1 and are not a machine check
of the full statements of Lemmas 5.3 and 8.6.
-/

namespace OpenAI086

/-!
Section 8.5, Lemma 8.6 (PDF p.70): the chain inclusion for i < N
alone does not imply P_N ⊆ C_N. The first two conjuncts model
P₁ ⊆ C₁ and C₁ ⊆ P₂, while the last refutes P₂ ⊆ C₂.
-/
theorem missing_last_endpoint_counterexample :
    (({0} : Finset ℕ) ⊆ ({0} : Finset ℕ)) ∧
    (({0} : Finset ℕ) ⊆ ({0} : Finset ℕ)) ∧
    ¬ (({0} : Finset ℕ) ⊆ ({1} : Finset ℕ)) := by
  simp

/-!
Section 5.2, Lemma 5.3 (PDF pp.32–33): a private input coordinate
contributes to the residual predictor identity. The following is its
one-cell REAL scalar model:

    μ + √ε (p - √ε a) = 0

where p is the corresponding private coordinate of the input.
-/
theorem predictor_identity_general
    (ε μ a p : ℝ) (hε : 0 ≤ ε)
    (hortho : μ + Real.sqrt ε * (p - Real.sqrt ε * a) = 0) :
    μ = ε * a - Real.sqrt ε * p := by
  have hs : Real.sqrt ε * Real.sqrt ε = ε := by
    simpa [pow_two] using Real.sq_sqrt hε
  calc
    μ = -Real.sqrt ε * (p - Real.sqrt ε * a) := by linarith
    _ = (Real.sqrt ε * Real.sqrt ε) * a - Real.sqrt ε * p := by ring
    _ = ε * a - Real.sqrt ε * p := by rw [hs]

/-- The shortened formula in the PDF follows with zero private input. -/
theorem predictor_identity_physical_input
    (ε μ a p : ℝ) (hε : 0 ≤ ε) (hp : p = 0)
    (hortho : μ + Real.sqrt ε * (p - Real.sqrt ε * a) = 0) :
    μ = ε * a := by
  have h := predictor_identity_general ε μ a p hε hortho
  simpa [hp] using h

/-- Without the zero-private-input assumption the shortened formula is false. -/
theorem predictor_shortcut_counterexample :
    ∃ ε μ a p : ℝ,
      0 ≤ ε ∧
      μ + Real.sqrt ε * (p - Real.sqrt ε * a) = 0 ∧
      μ ≠ ε * a := by
  refine ⟨1, 0, 1, 1, by norm_num, ?_, by norm_num⟩
  norm_num

/-!
Section 9.1 (PDF p.78): if role 1 is the FIRST failing role,
role 0 must have passed. This is a minimal Boolean check, not a
formalization of the paper's entire counting argument.
-/
theorem first_failure_second_role
    (b : Fin 3 → Bool) (h0 : b 0 = false) (h1 : b 1 = true) :
    (if b 0 then (0 : ℕ) else if b 1 then 1 else 2) = 1 := by
  simp [h0, h1]

end OpenAI086
