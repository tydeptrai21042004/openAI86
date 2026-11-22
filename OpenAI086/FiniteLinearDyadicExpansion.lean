import Mathlib
import OpenAI086.FiniteDyadicPrefixBlocks

/-!
# Operator-valued dyadic prefixes without commutativity

This is a linear-map version of the one-family telescoping calculation.
Unlike the earlier coordinate-only version, the result is an equality
of operators and can be used as an input to ordered operator products.

It is an algebraic sublemma of manuscript Lemma 3.3, NOT the row-prefix
logarithmic estimate and NOT a proof of the article's Lemma 3.3.
-/

namespace OpenAI086

/-- Real linear endomorphisms of a finite-dimensional Euclidean coordinate
space. Finite dimensionality is only a staging point for the full Hilbert
space estimate. -/
abbrev FiniteRealEnd (d : ℕ) :=
  (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)

/-- Increments with the essential initial `P 0` convention. -/
def finiteLinearIncrement {d : ℕ} (P : ℕ → FiniteRealEnd d) :
    ℕ → FiniteRealEnd d
  | 0 => P 0
  | n + 1 => P (n + 1) - P n

/-- Every finite telescoping prefix is exactly the final operator. -/
theorem finite_linear_increment_prefix {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), finiteLinearIncrement P k) = P N := by
  induction N with
  | zero => simp [finiteLinearIncrement]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      change P N + (P (N + 1) - P N) = P (N + 1)
      abel

/-- A block is a *sum of linear maps*, not a list of their values at a
chosen vector. -/
def finiteLinearBlock {d : ℕ} (P : ℕ → FiniteRealEnd d)
    (start width : ℕ) : FiniteRealEnd d :=
  ∑ j ∈ Finset.range width, finiteLinearIncrement P (start + j)

/-- Sum the intervals in the order produced by the constructive dyadic
prefix algorithm. -/
def finiteLinearBlockList {d : ℕ} (P : ℕ → FiniteRealEnd d) :
    List (ℕ × ℕ) → FiniteRealEnd d
  | [] => 0
  | (start, width) :: rest =>
      finiteLinearBlock P start width + finiteLinearBlockList P rest

/-- The operator-list sum agrees coordinatewise with the V5 scalar
block sum. -/
theorem finite_linear_block_list_apply {d : ℕ}
    (P : ℕ → FiniteRealEnd d)
    (blocks : List (ℕ × ℕ)) (x : Fin d → ℝ) (j : Fin d) :
    (finiteLinearBlockList P blocks) x j =
      finiteDyadicBlockSum
        (fun k => (finiteLinearIncrement P k) x j) blocks := by
  induction blocks with
  | nil => simp [finiteLinearBlockList, finiteDyadicBlockSum]
  | cons b rest ih =>
      obtain ⟨start, width⟩ := b
      simp only [finiteLinearBlockList, finiteDyadicBlockSum,
        LinearMap.add_apply, Pi.add_apply, finiteLinearBlock,
        LinearMap.sum_apply, Finset.sum_apply]
      rw [ih]

/-- Constructive exact operator identity for all prefixes (including
`P 0`). There are at most `k+1` blocks if `N+1 ≤ 2^k`, by the
independent theorem `finite_dyadic_prefix_length_le`. -/
theorem finite_linear_operator_dyadic_prefix {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k N : ℕ)
    (hN : N + 1 ≤ 2 ^ k) :
    finiteLinearBlockList P (finiteDyadicPrefixBlocks k 0 (N + 1)) = P N := by
  apply LinearMap.ext
  intro x
  funext j
  rw [finite_linear_block_list_apply]
  calc
    finiteDyadicBlockSum (fun i => (finiteLinearIncrement P i) x j)
        (finiteDyadicPrefixBlocks k 0 (N + 1)) =
        ∑ i ∈ Finset.range (N + 1), (finiteLinearIncrement P i) x j := by
          simpa only [zero_add] using
            (finite_dyadic_prefix_sum_exact
              (fun i => (finiteLinearIncrement P i) x j)
              k 0 (N + 1) hN)
    _ = P N x j := by
      have h := congrArg (fun A : FiniteRealEnd d => A x j)
        (finite_linear_increment_prefix P N)
      simpa [LinearMap.sum_apply, Finset.sum_apply] using h

end OpenAI086
