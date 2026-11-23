import Mathlib
import OpenAI086.FiniteLinearProjectionBlockBridge
import OpenAI086.AdaptiveNoncommutingRows

/-!
# V15: genuine prefix-increment Bessel rows with noncommuting layers

The existing generic noncommuting row theorem assumes a Bessel family
of block operators at each layer.  Here those blocks are constructed
from *actual* nested orthogonal projection families with the paper's
initial-increment convention.  Each layer may have a different block
width and each row may choose a different block in every layer.

This verifies the Bessel estimate for a FIXED tuple of block widths
and arbitrary noncommuting projection layers.  The next step of the
full Lemma 3.3 is to reconstruct every row's actual prefix product by
summing over only `O(log(T+1)^m)` such width tuples.
-/

namespace OpenAI086

/-- A single layer of actual dyadic increments, with a row-dependent
block index, obeys the exact row Bessel bound without depth loss. -/
theorem actual_dyadic_one_layer_adaptive_bessel
    {d count : ℕ} {Row : Type*} [Fintype Row]
    (P : ℕ → FiniteRealEnd d)
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (width : ℕ)
    (choice : Row → Fin count)
    (B : Row → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row,
      (B r (paperAlignedIncrementBlock
          (fun k y => P k y) width (choice r).val x)) ^ 2) ≤
      finiteRealPair x x := by
  classical
  apply finite_adaptive_row_bessel
    B
    (fun b : Fin count =>
      paperAlignedIncrementBlock (fun k y => P k y) width b.val x)
    choice (finiteRealPair x x) hrow
  have h := paper_aligned_increment_bessel
    (fun k y => P k y) hsym hidemp hnested width count x
  simpa only [Fin.sum_univ_eq_sum_range] using h

/-- Actual nested projection increments for an arbitrary finite
ordered product. Every layer has its own width; row choices can vary
in every layer, and no layers are assumed to commute. -/
theorem actual_dyadic_noncommuting_tuple_bessel
    {d count : ℕ} {Row Layer : Type*} [Fintype Row]
    (P : Layer → ℕ → FiniteRealEnd d)
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (hnested : ∀ i k u, P i k (P i (k + 1) u) = P i k u)
    (width : Layer → ℕ)
    (choice : Layer → Row → Fin count)
    (layers : List Layer)
    (B : Row → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row,
      (B r (adaptiveNoncommutingProduct
        (fun i b y => paperAlignedIncrementBlock
          (fun k z => P i k z) (width i) b.val y)
        choice r layers x)) ^ 2) ≤
      finiteRealPair x x := by
  classical
  let Q : Layer → ℕ → (Fin d → ℝ) → (Fin d → ℝ) :=
    fun i => withZeroInitialProjection (fun k y => P i k y)
  have hsymQ : ∀ i k u v,
      finiteRealPair (Q i k u) v = finiteRealPair u (Q i k v) := by
    intro i
    exact with_zero_initial_self_adjoint (fun k y => P i k y) (hsym i)
  have hidempQ : ∀ i k u, Q i k (Q i k u) = Q i k u := by
    intro i
    exact with_zero_initial_idempotent (fun k y => P i k y) (hidemp i)
  have hnestedQ : ∀ i k u, Q i k (Q i (k + 1) u) = Q i k u := by
    intro i
    exact with_zero_initial_nested (fun k y => P i k y) (hnested i)
  have hcut : ∀ i k, k * width i ≤ (k + 1) * width i := by
    intro i k
    exact Nat.mul_le_mul_right (width i) (Nat.le_succ k)
  have h := adaptive_nested_projection_row_bessel
    Q hsymQ hidempQ hnestedQ
    (fun i k => k * width i) hcut choice layers B hrow x
  -- This equality is definitional: the actual block is the
  -- difference of the augmented projections at adjacent width multiples.
  have hQ :
      (fun i b y => variableProjectionBlock (Q i)
        (fun k => k * width i) b.val y) =
      (fun i b y => paperAlignedIncrementBlock
        (fun k z => P i k z) (width i) b.val y) := by
    funext i b y
    rfl
  rw [hQ] at h
  exact h

end OpenAI086
