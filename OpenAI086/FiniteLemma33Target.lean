import Mathlib
import OpenAI086.GeneralNestedProjectionEnergy

/-!
# Explicit finite-real main goals for Lemma 3.3 (V6)

Unlike the generic target catalog, these are typed formulas with the
actual nested orthogonal projection hypotheses, row-Bessel condition,
noncommutative ordered products, and a logarithmic factor.

They are **definitions of open propositions**, NOT proofs.  The
logarithmic factor is a slightly relaxed dyadic envelope: 2+Nat.log2(T+1).
The actual paper is for arbitrary complex Hilbert spaces, and also
requires an exact constant as specified in the source.
-/

namespace OpenAI086

/-- Apply `m` indexed operators in order at level `n`, allowing
operators from different families to fail to commute. -/
def finiteSequentialProjectionProduct {d : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (m n : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  (List.range m).foldl (fun z i => P i n z) x

/-- Genuine finite-dimensional hypotheses: symmetry (self-adjointness),
idempotence and nestedness within each family. -/
def finiteNestedProjectionSystem {d : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ)) (m : ℕ) : Prop :=
  ∀ i < m,
    (∀ n u v,
      finiteRealPair (P i n u) v = finiteRealPair u (P i n v)) ∧
    (∀ n u, P i n (P i n u) = P i n u) ∧
    (∀ n u, P i n (P i (n + 1) u) = P i n u)

/-- An explicit dyadic logarithm envelope (at least the manuscript's
`1+ceil(log₂(T+1))`). -/
def finitePrefixLogEnvelope (T : ℕ) : ℝ :=
  (Nat.log2 (T + 1) + 2 : ℕ)

/-- OPEN: finite-dimensional real row-prefix estimate, including the
variable prefix selected separately by each row. This is not an axiom:
it is an unproved `Prop` used to state exactly what remains. -/
def finiteLemma33RowPrefixGoal {d : ℕ}
    (m T rows : ℕ)
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (B : Fin rows → (Fin d → ℝ) → ℝ)
    (choice : Fin rows → Fin (T + 1)) : Prop :=
  finiteNestedProjectionSystem P m →
  (∀ y : Fin d → ℝ,
    (∑ r : Fin rows, (B r y) ^ 2) ≤ finiteRealPair y y) →
  ∀ x : Fin d → ℝ,
    (∑ r : Fin rows,
      (B r (finiteSequentialProjectionProduct P m (choice r).val x)) ^ 2) ≤
      (finitePrefixLogEnvelope T) ^ (2 * m) * finiteRealPair x x

/-- OPEN: the corresponding square-variation inequality for the same
actual ordered products. This must not be inferred solely from the
single-family variation lemma. -/
def finiteLemma33VariationGoal {d : ℕ}
    (m T : ℕ)
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  finiteNestedProjectionSystem P m →
  ∀ x : Fin d → ℝ,
    (∑ n ∈ Finset.range T,
      finiteRealPair
        (fun j => finiteSequentialProjectionProduct P m (n + 1) x j -
          finiteSequentialProjectionProduct P m n x j)
        (fun j => finiteSequentialProjectionProduct P m (n + 1) x j -
          finiteSequentialProjectionProduct P m n x j)) ≤
      (m : ℝ) ^ 2 * (finitePrefixLogEnvelope T) ^ (2 * (m - 1)) *
        finiteRealPair x x

end OpenAI086
