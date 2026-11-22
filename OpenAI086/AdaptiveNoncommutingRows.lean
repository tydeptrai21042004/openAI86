import Mathlib
import OpenAI086.FiniteAdaptiveRowBessel
import OpenAI086.FiniteVariableProjectionBlocks

/-!
# Adaptive rows through arbitrary noncommuting Bessel layers

This module establishes a substantial missing assembly step in the binary-prefix
argument of manuscript Lemma 3.3. For every row r and every layer i, the row
may choose a DIFFERENT block. If each layer is Bessel-contracting and the final
rows are Bessel-contracting, the resulting adaptive, noncommuting products are
Bessel-contracting with constant exactly one. Neither the row count, layer
count, nor block count appears in the bound.

In the second theorem, every Bessel layer is constructed from actual increments
of a finite-dimensional real family of nested orthogonal projections. Thus no
abstract 'block energy' is supplied as a theorem hypothesis in that application.

The full Lemma 3.3 needs the independent binary-prefix partition identity and
the summation over dyadic block LENGTHS to produce L_T^m, and then its variation
inequality. This module does not claim those remaining results.
-/

namespace OpenAI086

/-- Ordered action: the head of `layers` acts first. Choices may depend
on the row and the layer; distinct layers need not commute. -/
def adaptiveNoncommutingProduct
    {n : ℕ} {Row Layer Block : Type*}
    (Q : Layer → Block → (Fin n → ℝ) → (Fin n → ℝ))
    (choice : Layer → Row → Block) (r : Row) :
    List Layer → (Fin n → ℝ) → (Fin n → ℝ)
  | [], x => x
  | i :: rest, x =>
      adaptiveNoncommutingProduct Q choice r rest (Q i (choice i r) x)

/-- Adaptive row-Bessel inequality for ANY finite ordered list of
noncommuting Bessel layers. A row can select its own block at every
layer. No commutativity, linearity or block-size assumption is used. -/
theorem adaptive_noncommuting_row_bessel
    {n : ℕ} {Row Layer Block : Type*}
    [Fintype Row] [Fintype Block]
    (Q : Layer → Block → (Fin n → ℝ) → (Fin n → ℝ))
    (choice : Layer → Row → Block)
    (hblock : ∀ i : Layer, ∀ y : Fin n → ℝ,
      (∑ b : Block, finiteRealPair (Q i b y) (Q i b y)) ≤
        finiteRealPair y y) :
    ∀ (layers : List Layer) (B : Row → (Fin n → ℝ) → ℝ),
      (∀ y : Fin n → ℝ,
        (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y) →
      ∀ x : Fin n → ℝ,
        (∑ r : Row,
          (B r (adaptiveNoncommutingProduct Q choice r layers x)) ^ 2) ≤
          finiteRealPair x x := by
  classical
  intro layers
  induction layers with
  | nil =>
      intro B hrow x
      simpa [adaptiveNoncommutingProduct] using hrow x
  | cons i rest ih =>
      intro B hrow x
      have hrest : ∀ y : Fin n → ℝ,
          (∑ r : Row,
            (B r (adaptiveNoncommutingProduct Q choice r rest y)) ^ 2) ≤
            finiteRealPair y y := by
        intro y
        exact ih B hrow y
      have hstep := finite_adaptive_row_bessel
        (fun r y => B r (adaptiveNoncommutingProduct Q choice r rest y))
        (fun b : Block => Q i b x) (choice i) (finiteRealPair x x)
        hrest (hblock i x)
      simpa only [adaptiveNoncommutingProduct] using hstep

/-- A concrete finite-dimensional real m-layer form. Each layer i is
built from its *own* nested projection family, with an independently
chosen monotone cut sequence and arbitrary per-row block selection.
The families may be noncommuting. The sharp Bessel constant remains 1.

This is the fixed-length-tuple Bessel part of the paper's first Lemma 3.3
estimate, not the logarithmic assembly across block-length tuples. -/
theorem adaptive_nested_projection_row_bessel
    {n count : ℕ} {Row Layer : Type*} [Fintype Row]
    (P : Layer → ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (hnested : ∀ i k u, P i k (P i (k + 1) u) = P i k u)
    (cut : Layer → ℕ → ℕ)
    (hcut : ∀ i k, cut i k ≤ cut i (k + 1))
    (choice : Layer → Row → Fin count)
    (layers : List Layer)
    (B : Row → (Fin n → ℝ) → ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin n → ℝ) :
    (∑ r : Row,
      (B r (adaptiveNoncommutingProduct
        (fun i b y => variableProjectionBlock (P i) (cut i) b.val y)
        choice r layers x)) ^ 2) ≤ finiteRealPair x x := by
  classical
  apply adaptive_noncommuting_row_bessel
    (fun i b y => variableProjectionBlock (P i) (cut i) b.val y)
    choice ?_ layers B hrow x
  intro i y
  have h := variable_projection_block_energy_bound (P i)
    (hsym i) (hidemp i) (hnested i)
    (cut i) (hcut i) count y
  simpa only [Finset.sum_range] using h

/-- Sum over arbitrary *different* tuples of block-size classes. Every
individual class has Bessel constant one; summing classes incurs exactly
the square of their number. In Lemma 3.3 there are at most `L_T ^ m`
classes, one for each tuple of dyadic block lengths. -/
theorem multilevel_adaptive_noncommuting_row_bessel
    {n : ℕ} {Row Layer Block Level : Type*}
    [Fintype Row] [Fintype Block] [Fintype Level]
    (Q : Level → Layer → Block → (Fin n → ℝ) → (Fin n → ℝ))
    (choice : Level → Layer → Row → Block)
    (layers : Level → List Layer)
    (B : Row → (Fin n → ℝ) → ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (hblock : ∀ k : Level, ∀ i : Layer, ∀ y : Fin n → ℝ,
      (∑ b : Block,
        finiteRealPair (Q k i b y) (Q k i b y)) ≤ finiteRealPair y y)
    (x : Fin n → ℝ) :
    (∑ r : Row,
      (∑ k : Level,
        B r (adaptiveNoncommutingProduct (Q k) (choice k) r (layers k) x)) ^ 2)
       ≤ (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  apply finite_level_row_square_bound
    (fun k r => B r
      (adaptiveNoncommutingProduct (Q k) (choice k) r (layers k) x))
    (finiteRealPair x x)
  intro k
  exact adaptive_noncommuting_row_bessel
    (Q k) (choice k) (hblock k) (layers k) B hrow x

/-- All the analytic row and layer estimates are proved ABOVE. The
remaining `hdecomp` is precisely the combinatorial binary-prefix
identity for the actual row outputs, and is intentionally explicit.
No false completion of Lemma 3.3 is claimed. -/
theorem prefix_from_noncommuting_block_expansion
    {n : ℕ} {Row Layer Block Level : Type*}
    [Fintype Row] [Fintype Block] [Fintype Level]
    (Q : Level → Layer → Block → (Fin n → ℝ) → (Fin n → ℝ))
    (choice : Level → Layer → Row → Block)
    (layers : Level → List Layer)
    (B : Row → (Fin n → ℝ) → ℝ)
    (target : Row → ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (hblock : ∀ k : Level, ∀ i : Layer, ∀ y : Fin n → ℝ,
      (∑ b : Block,
        finiteRealPair (Q k i b y) (Q k i b y)) ≤ finiteRealPair y y)
    (x : Fin n → ℝ)
    (hdecomp : ∀ r : Row,
      target r = ∑ k : Level,
        B r (adaptiveNoncommutingProduct (Q k) (choice k) r (layers k) x)) :
    (∑ r : Row, (target r) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x := by
  calc
    (∑ r : Row, (target r) ^ 2) =
        ∑ r : Row,
          (∑ k : Level,
            B r (adaptiveNoncommutingProduct (Q k) (choice k) r (layers k) x)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hdecomp r]
    _ ≤ (Fintype.card Level : ℝ) ^ 2 * finiteRealPair x x :=
      multilevel_adaptive_noncommuting_row_bessel
        Q choice layers B hrow hblock x

end OpenAI086
