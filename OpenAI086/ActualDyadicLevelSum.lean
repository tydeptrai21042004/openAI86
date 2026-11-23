import Mathlib
import OpenAI086.ActualDyadicTupleBessel
import OpenAI086.FiniteAdaptiveRowBessel

/-!
# V15: full finite-length-tuple energy assembly from real projections

Unlike the earlier generic assembly, this one uses concrete dyadic
increments of actual nested orthogonal projections with a ZERO initial
projection. For every fixed length tuple there is no loss from the
number of rows, block positions, or noncommuting layers. Summing `K`
length tuples costs `K²` in squared energy (the Rademacher--Menshov
assembly step).

This is NOT yet the complete prefix theorem of Lemma 3.3: a separate
combinatorial identity must identify the SUM on the left with every
row's desired ordered product at its own selected depth. No such
identity is assumed in the theorem below.
-/

namespace OpenAI086

/-- Actual-projection form of the abstract multilevel noncommuting
Bessel inequality, with per-level/per-layer widths and per-row choices. -/
theorem actual_dyadic_multilevel_noncommuting_bessel
    {d count : ℕ} {Row Layer Level : Type*}
    [Fintype Row] [Fintype Level]
    (P : Layer → ℕ → FiniteRealEnd d)
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (hnested : ∀ i k u, P i k (P i (k + 1) u) = P i k u)
    (width : Level → Layer → ℕ)
    (choice : Level → Layer → Row → Fin count)
    (layers : List Layer)
    (B : Row → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row,
      (∑ a : Level,
        B r (adaptiveNoncommutingProduct
          (fun i b y => paperAlignedIncrementBlock
            (fun k z => P i k z) (width a i) b.val y)
          (choice a) r layers x)) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  apply finite_level_row_square_bound
    (fun a r => B r (adaptiveNoncommutingProduct
      (fun i b y => paperAlignedIncrementBlock
        (fun k z => P i k z) (width a i) b.val y)
      (choice a) r layers x))
    (finiteRealPair x x)
  intro a
  exact actual_dyadic_noncommuting_tuple_bessel
    P hsym hidemp hnested (width a) (choice a) layers B hrow x

/-- A precise FINAL outstanding reduction for the finite-real
row-prefix theorem. The `hdecomp` premise is a mathematical statement,
not a Lean `axiom`: the row-specific dyadic-length decomposition must
be constructed and proved before this implication can complete Lemma 3.3.
The previous theorem establishes every energy hypothesis without any
externally supplied `hblock` assumption. -/
theorem actual_dyadic_row_prefix_reduction
    {d count : ℕ} {Row Layer Level : Type*}
    [Fintype Row] [Fintype Level]
    (P : Layer → ℕ → FiniteRealEnd d)
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (hnested : ∀ i k u, P i k (P i (k + 1) u) = P i k u)
    (width : Level → Layer → ℕ)
    (choice : Level → Layer → Row → Fin count)
    (layers : List Layer)
    (B : Row → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (target : Row → ℝ) (x : Fin d → ℝ)
    (hdecomp : ∀ r : Row,
      target r = ∑ a : Level,
        B r (adaptiveNoncommutingProduct
          (fun i b y => paperAlignedIncrementBlock
            (fun k z => P i k z) (width a i) b.val y)
          (choice a) r layers x)) :
    (∑ r : Row, (target r) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  have h := actual_dyadic_multilevel_noncommuting_bessel
    P hsym hidemp hnested width choice layers B hrow x
  calc
    (∑ r : Row, (target r) ^ 2) =
      ∑ r : Row,
        (∑ a : Level,
          B r (adaptiveNoncommutingProduct
            (fun i b y => paperAlignedIncrementBlock
              (fun k z => P i k z) (width a i) b.val y)
            (choice a) r layers x)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro r _
              rw [hdecomp r]
    _ ≤ (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := h

/-- Specialization to *genuinely linear* row maps, so a vector-valued
identity for ordered prefix products is sufficient. This matches the
linearity requirement in the manuscript and in `finiteLemma33RowPrefixGoal`.
It is a reduction rather than the missing vector decomposition theorem. -/
theorem actual_dyadic_linear_row_prefix_reduction
    {d count : ℕ} {Row Layer Level : Type*}
    [Fintype Row] [Fintype Level]
    (P : Layer → ℕ → FiniteRealEnd d)
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (hnested : ∀ i k u, P i k (P i (k + 1) u) = P i k u)
    (width : Level → Layer → ℕ)
    (choice : Level → Layer → Row → Fin count)
    (layers : List Layer)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (target : Row → (Fin d → ℝ)) (x : Fin d → ℝ)
    (hvector : ∀ r : Row,
      target r = ∑ a : Level,
        adaptiveNoncommutingProduct
          (fun i b y => paperAlignedIncrementBlock
            (fun k z => P i k z) (width a i) b.val y)
          (choice a) r layers x) :
    (∑ r : Row, (B r (target r)) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  classical
  apply actual_dyadic_row_prefix_reduction P hsym hidemp hnested
    width choice layers (fun r y => B r y) hrow
    (fun r => B r (target r)) x
  intro r
  rw [hvector r]
  exact map_sum (B r)
    (fun a : Level => adaptiveNoncommutingProduct
      (fun i b y => paperAlignedIncrementBlock
        (fun k z => P i k z) (width a i) b.val y)
      (choice a) r layers x) Finset.univ

end OpenAI086
