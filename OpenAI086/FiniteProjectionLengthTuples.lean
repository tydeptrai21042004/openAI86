import Mathlib
import OpenAI086.AdaptiveNoncommutingRows

/-!
# Direct multilevel Bessel estimate from genuinely nested projection blocks

The earlier assembly theorem used abstract Bessel maps at every level. Here
we supply those Bessel maps by the actual differences of nested orthogonal
projections, with independent projection families, cut sequences, layer
orders, and row choices at EACH level.

The only hypothesis left in the final bridge is that a particular target
row output can be expanded into the supplied block-length configurations.
This is exactly the missing binary-prefix identity for manuscript Lemma 3.3;
no version of that identity is assumed in the unconditional energy theorem.
-/

namespace OpenAI086

/-- At every level, rows may choose different blocks in each of an
arbitrary ordered number of potentially noncommuting projection families.
Their level sum has squared-energy factor exactly (number of levels)^2.
No independently asserted block-energy budget is needed. -/
theorem finite_projection_length_tuple_rows
    {n count : ℕ} {Row Layer Level : Type*}
    [Fintype Row] [Fintype Level]
    (P : Level → Layer → ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ a i k u v,
      finiteRealPair (P a i k u) v = finiteRealPair u (P a i k v))
    (hidemp : ∀ a i k u, P a i k (P a i k u) = P a i k u)
    (hnested : ∀ a i k u, P a i k (P a i (k + 1) u) = P a i k u)
    (cut : Level → Layer → ℕ → ℕ)
    (hcut : ∀ a i k, cut a i k ≤ cut a i (k + 1))
    (choice : Level → Layer → Row → Fin count)
    (layers : Level → List Layer)
    (B : Row → (Fin n → ℝ) → ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin n → ℝ) :
    (∑ r : Row,
      (∑ a : Level,
        B r (adaptiveNoncommutingProduct
          (fun i b y => variableProjectionBlock (P a i) (cut a i) b.val y)
          (choice a) r (layers a) x)) ^ 2) ≤
        (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  apply finite_level_row_square_bound
    (fun a r => B r (adaptiveNoncommutingProduct
      (fun i b y => variableProjectionBlock (P a i) (cut a i) b.val y)
      (choice a) r (layers a) x))
    (finiteRealPair x x)
  intro a
  exact adaptive_nested_projection_row_bessel
    (P a) (hsym a) (hidemp a) (hnested a)
    (cut a) (hcut a) (choice a) (layers a) B hrow x

/-- An explicit row-level bridge for a concrete target `target`.
`hdecomp` cannot be dropped until the binary-prefix partition is
constructed and connected to the ordered projection product. -/
theorem finite_projection_prefix_from_length_tuple_expansion
    {n count : ℕ} {Row Layer Level : Type*}
    [Fintype Row] [Fintype Level]
    (P : Level → Layer → ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ a i k u v,
      finiteRealPair (P a i k u) v = finiteRealPair u (P a i k v))
    (hidemp : ∀ a i k u, P a i k (P a i k u) = P a i k u)
    (hnested : ∀ a i k u, P a i k (P a i (k + 1) u) = P a i k u)
    (cut : Level → Layer → ℕ → ℕ)
    (hcut : ∀ a i k, cut a i k ≤ cut a i (k + 1))
    (choice : Level → Layer → Row → Fin count)
    (layers : Level → List Layer)
    (B : Row → (Fin n → ℝ) → ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin n → ℝ)
    (target : Row → ℝ)
    (hdecomp : ∀ r : Row,
      target r = ∑ a : Level,
        B r (adaptiveNoncommutingProduct
          (fun i b y => variableProjectionBlock (P a i) (cut a i) b.val y)
          (choice a) r (layers a) x)) :
    (∑ r : Row, (target r) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  calc
    (∑ r : Row, (target r) ^ 2) =
        ∑ r : Row,
          (∑ a : Level,
            B r (adaptiveNoncommutingProduct
              (fun i b y => variableProjectionBlock (P a i) (cut a i) b.val y)
              (choice a) r (layers a) x)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hdecomp r]
    _ ≤ (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x :=
      finite_projection_length_tuple_rows P hsym hidemp hnested
        cut hcut choice layers B hrow x

end OpenAI086
