import Mathlib

/-!
# Independent noncommutative product identities (OpenAI #086, Lemma 3.3)

An algebraic component of the difference of two *ordered* products of
noncommuting operators. The product is implemented as a list fold, so no
commutativity is silently assumed. This does NOT establish the Hilbert-space
Rademacher--Menshov estimate or the logarithmic row bound in Lemma 3.3.

The mathematical idea (ordered telescoping before estimating each row) was
reviewed against the reference project's `RademacherMenshov.lean`. The code,
names and proofs in this file are independently written, and only Mathlib
is imported.
-/

namespace OpenAI086

/-- Ordered product of the first coordinates. -/
def orderedLeft {R : Type*} [Monoid R] : List (R × R) → R
  | [] => 1
  | p :: ps => p.1 * orderedLeft ps

/-- Ordered product of the second coordinates, preserving the same order. -/
def orderedRight {R : Type*} [Monoid R] : List (R × R) → R
  | [] => 1
  | p :: ps => p.2 * orderedRight ps

/-- Algebraic ordered-product increment expansion. -/
def orderedDifference {R : Type*} [Ring R] : List (R × R) → R
  | [] => 0
  | p :: ps =>
      (p.1 - p.2) * orderedLeft ps + p.2 * orderedDifference ps

/-- Two-factor rearrangement. Valid in every ring, *including noncommutative* ones. -/
theorem two_factor_difference {R : Type*} [Ring R] (a b u v : R) :
    a * u - b * v = (a - b) * u + b * (u - v) := by
  simp only [sub_mul, mul_sub]
  abel

/-- Exact algebraic telescoping for an arbitrary number of noncommuting factors.
It is not an estimate and has no Hilbert-space projection hypotheses. -/
theorem ordered_difference_correct {R : Type*} [Ring R]
    (pairs : List (R × R)) :
    orderedLeft pairs - orderedRight pairs = orderedDifference pairs := by
  induction pairs with
  | nil => simp [orderedLeft, orderedRight, orderedDifference]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      change a * orderedLeft ps - b * orderedRight ps =
        (a - b) * orderedLeft ps + b * orderedDifference ps
      rw [← ih]
      exact two_factor_difference a b (orderedLeft ps) (orderedRight ps)

/-- Triangle-inequality budget for differences of ordered products.
This is a *coarse* bound; it has no logarithmic Rademacher--Menshov saving. -/
def orderedErrorBudget {R : Type*} [NormedRing R] : List (R × R) → ℝ
  | [] => 0
  | p :: ps =>
      ‖p.1 - p.2‖ * ‖orderedLeft ps‖ + ‖p.2‖ * orderedErrorBudget ps

/-- A general, noncommutative, normed-ring product-error estimate. -/
theorem ordered_difference_norm_le {R : Type*} [NormedRing R]
    (pairs : List (R × R)) :
    ‖orderedLeft pairs - orderedRight pairs‖ ≤ orderedErrorBudget pairs := by
  induction pairs with
  | nil => simp [orderedLeft, orderedRight, orderedErrorBudget]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      change ‖a * orderedLeft ps - b * orderedRight ps‖ ≤
        ‖a - b‖ * ‖orderedLeft ps‖ + ‖b‖ * orderedErrorBudget ps
      calc
        ‖a * orderedLeft ps - b * orderedRight ps‖ =
            ‖(a - b) * orderedLeft ps +
              b * (orderedLeft ps - orderedRight ps)‖ := by
                congr 1
                exact two_factor_difference a b (orderedLeft ps) (orderedRight ps)
        _ ≤ ‖(a - b) * orderedLeft ps‖ +
              ‖b * (orderedLeft ps - orderedRight ps)‖ := norm_add_le _ _
        _ ≤ ‖a - b‖ * ‖orderedLeft ps‖ +
              ‖b‖ * ‖orderedLeft ps - orderedRight ps‖ := by
                exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ‖a - b‖ * ‖orderedLeft ps‖ + ‖b‖ * orderedErrorBudget ps := by
                exact add_le_add (le_refl _)
                  (mul_le_mul_of_nonneg_left ih (norm_nonneg b))

end OpenAI086
