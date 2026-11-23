import Mathlib

/-!
# Lemma 5.3: exact corrected predictor identity on an arbitrary finite cell

This develops the real finite-weighted analogue of the augmented-column
orthogonality relation in the manuscript. Unlike the old scalar example,
this result quantifies over the whole cell and keeps the private-component
AVERAGE of the actual input. It is a rigorous algebraic ingredient for a
future projection/conditional-expectation formalization of equation (7).

It is not an analytic proof of Lemma 5.3, and requires a kernel build before
being reported as Lean-verified.
-/

namespace OpenAI086

/-- If the augmented predictor `(ψ, √ε e_p)` is orthogonal to the
projection residual on a normalized weighted finite cell, the physical
predictor moment includes the private input average. -/
theorem finite_predictor_weighted_orthogonality
    {n : ℕ} (w f ψ privateInput : Fin n → ℝ)
    (ε a : ℝ) (hε : 0 ≤ ε)
    (hw : (∑ i : Fin n, w i) = 1)
    (hortho : (∑ i : Fin n,
      w i * (((f i - a * ψ i) * ψ i) +
        Real.sqrt ε * (privateInput i - Real.sqrt ε * a))) = 0) :
    (∑ i : Fin n, w i * ((f i - a * ψ i) * ψ i)) =
      ε * a - Real.sqrt ε * (∑ i : Fin n, w i * privateInput i) := by
  have hs : Real.sqrt ε * Real.sqrt ε = ε := by
    simpa [pow_two] using Real.sq_sqrt hε
  have expand :
      (∑ i : Fin n,
        w i * (((f i - a * ψ i) * ψ i) +
          Real.sqrt ε * (privateInput i - Real.sqrt ε * a))) =
        (∑ i : Fin n, w i * ((f i - a * ψ i) * ψ i)) +
          Real.sqrt ε * (∑ i : Fin n, w i * privateInput i) -
          (Real.sqrt ε * Real.sqrt ε * a) * (∑ i : Fin n, w i) := by
    calc
      _ = ∑ i : Fin n,
          (w i * ((f i - a * ψ i) * ψ i) +
            Real.sqrt ε * (w i * privateInput i) -
            (Real.sqrt ε * Real.sqrt ε * a) * w i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = _ := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]
  rw [expand, hw, hs] at hortho
  linarith

/-- The shorter manuscript identity is valid if the weighted private
input mean is zero (e.g. for a purely physical input). -/
theorem finite_predictor_weighted_physical_input
    {n : ℕ} (w f ψ privateInput : Fin n → ℝ)
    (ε a : ℝ) (hε : 0 ≤ ε)
    (hw : (∑ i : Fin n, w i) = 1)
    (hp : (∑ i : Fin n, w i * privateInput i) = 0)
    (hortho : (∑ i : Fin n,
      w i * (((f i - a * ψ i) * ψ i) +
        Real.sqrt ε * (privateInput i - Real.sqrt ε * a))) = 0) :
    (∑ i : Fin n, w i * ((f i - a * ψ i) * ψ i)) = ε * a := by
  have h := finite_predictor_weighted_orthogonality
    w f ψ privateInput ε a hε hw hortho
  simpa [hp] using h

end OpenAI086
