import Mathlib
import OpenAI086.FiniteDyadicPrefixBlocks

/-!
# V6: operator-valued finite dyadic-prefix identity

The binary-prefix partition in V5 was scalar-valued.  The present module
specializes it to every coordinate of a (not necessarily commuting) family
of finite-dimensional real operators and proves the exact telescoping identity
for **one** family.  No projection, self-adjointness, or commutativity
hypothesis is needed for this algebraic identity.

This is a genuine piece of the missing `hdecomp` from Lemma 3.3, but it is
NOT the final product expansion for m independently varying families.
-/

namespace OpenAI086

/-- The initial increment includes `P₀`; all subsequent increments are
`Pₙ₊₁ − Pₙ`.  Keeping the initial term is essential in the paper's
`{0, ..., T}` indexing convention. -/
def finiteOperatorIncrement {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ)) :
    ℕ → (Fin d → ℝ) → (Fin d → ℝ)
  | 0 => P 0
  | n + 1 => fun x j => P (n + 1) x j - P n x j

/-- Exact telescoping of a prefix of operator increments, evaluated
coordinatewise; no property of `P` is assumed. -/
theorem finite_operator_increment_prefix_exact {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (N : ℕ) (x : Fin d → ℝ) (j : Fin d) :
    (∑ i ∈ Finset.range (N + 1), finiteOperatorIncrement P i x j) =
      P N x j := by
  induction N with
  | zero =>
      simp [finiteOperatorIncrement]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      change P N x j + (P (N + 1) x j - P N x j) = P (N + 1) x j
      ring

/-- An explicit *single-family* dyadic block expansion from the V5
constructive prefix algorithm to the original operator prefix. This
statement discharges the initial-P₀ convention, but not distribution of
products across several independent families. -/
theorem finite_operator_prefix_dyadic_blocks {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (k N : ℕ) (hN : N + 1 ≤ 2 ^ k)
    (x : Fin d → ℝ) (j : Fin d) :
    finiteDyadicBlockSum (fun i => finiteOperatorIncrement P i x j)
        (finiteDyadicPrefixBlocks k 0 (N + 1)) = P N x j := by
  calc
    finiteDyadicBlockSum (fun i => finiteOperatorIncrement P i x j)
        (finiteDyadicPrefixBlocks k 0 (N + 1)) =
          ∑ i ∈ Finset.range (N + 1), finiteOperatorIncrement P i x j := by
            simpa only [zero_add] using
              (finite_dyadic_prefix_sum_exact
                (fun i => finiteOperatorIncrement P i x j)
                k 0 (N + 1) hN)
    _ = P N x j := finite_operator_increment_prefix_exact P N x j

/-- Equivalent extensional formulation: the dyadic block identity
holds simultaneously at every vector coordinate. -/
theorem finite_operator_prefix_dyadic_ext {d : ℕ}
    (P : ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (k N : ℕ) (hN : N + 1 ≤ 2 ^ k)
    (x : Fin d → ℝ) :
    (fun j => finiteDyadicBlockSum
      (fun i => finiteOperatorIncrement P i x j)
      (finiteDyadicPrefixBlocks k 0 (N + 1))) = P N x := by
  funext j
  exact finite_operator_prefix_dyadic_blocks P k N hN x j

end OpenAI086
