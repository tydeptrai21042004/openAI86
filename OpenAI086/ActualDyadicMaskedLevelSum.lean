import Mathlib
import OpenAI086.ActualDyadicLevelSum

/-!
# V16: Bessel energy for padded dyadic width tuples

At a fixed width tuple, a row may have no block of a specified width.
The grouped prefix expansion then contributes ZERO in that row. This
module establishes that zero masks do not spoil the sharp Bessel row
estimate for ordered, potentially noncommuting projection products.

The theorem does not assume a prior prefix decomposition. It uses the
already implemented actual-projection tuple Bessel inequality. In the
remaining Lemma 3.3 connection, the mask must be constructed from the
presence of a block of each width in the chosen row prefix.
-/

namespace OpenAI086

/-- Row contraction is preserved when any subset of rows is set to zero.
No linearity beyond that already needed in the original row estimates
is introduced by the mask. -/
theorem masked_finite_row_contraction
    {d : ℕ} {Row : Type*} [Fintype Row]
    (B : Row → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (active : Row → Bool) (y : Fin d → ℝ) :
    (∑ r : Row, (if active r then B r y else 0) ^ 2) ≤
      finiteRealPair y y := by
  calc
    (∑ r : Row, (if active r then B r y else 0) ^ 2) ≤
        ∑ r : Row, (B r y) ^ 2 := by
          apply Finset.sum_le_sum
          intro r _
          cases ha : active r with
          | false => simp [ha]; positivity
          | true => simp [ha]
    _ ≤ finiteRealPair y y := hrow y

/-- A fixed tuple of actual aligned projection blocks retains the
exact Bessel constant one even if its row contributions are selectively
zeroed. The mask may depend on the row and on the width tuple. -/
theorem actual_dyadic_masked_tuple_bessel
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
    (active : Row → Bool) (x : Fin d → ℝ) :
    (∑ r : Row,
      (if active r then
        B r (adaptiveNoncommutingProduct
          (fun i b y => paperAlignedIncrementBlock
            (fun n z => P i n z) (width i) b.val y)
          choice r layers x)
       else 0) ^ 2) ≤ finiteRealPair x x := by
  have hmasked : ∀ y : Fin d → ℝ,
      (∑ r : Row, (if active r then B r y else 0) ^ 2) ≤
        finiteRealPair y y :=
    masked_finite_row_contraction B hrow active
  exact actual_dyadic_noncommuting_tuple_bessel
    P hsym hidemp hnested width choice layers
    (fun r y => if active r then B r y else 0) hmasked x

/-- Uniform squared-energy bound for any finite collection of masked
width tuples. Both the masks and the aligned positions may depend on
the tuple and on the row. The factor `K²` is the level-summation loss,
where `K` is the number of width tuples. -/
theorem actual_dyadic_masked_multilevel_bessel
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
    (active : Level → Row → Bool) (x : Fin d → ℝ) :
    (∑ r : Row,
      (∑ a : Level,
        if active a r then
          B r (adaptiveNoncommutingProduct
            (fun i b y => paperAlignedIncrementBlock
              (fun n z => P i n z) (width a i) b.val y)
            (choice a) r layers x)
        else 0) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  apply finite_level_row_square_bound
    (fun a r => if active a r then
      B r (adaptiveNoncommutingProduct
        (fun i b y => paperAlignedIncrementBlock
          (fun n z => P i n z) (width a i) b.val y)
        (choice a) r layers x)
      else 0)
    (finiteRealPair x x)
  intro a
  exact actual_dyadic_masked_tuple_bessel
    P hsym hidemp hnested (width a) (choice a) layers
    B hrow (active a) x

end OpenAI086
