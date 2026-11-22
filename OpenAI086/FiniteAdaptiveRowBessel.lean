import Mathlib
import OpenAI086.FiniteRowCauchySchwarz
import OpenAI086.GeneralNestedProjectionEnergy

/-!
# Lemma 3.3: adaptive-row Bessel assembly and a finite level bound

The paper's first logarithmic estimate uses dyadic blocks and a row
contraction.  These lemmas establish the **exact row-grouping and
finite-level summation** implications of that argument for finite real
Euclidean signals; the block projections need not be coordinate masks.

No extra factors depending on the number of rows or blocks occur.
To obtain Lemma 3.3 it remains to construct orthogonal dyadic blocks
from nested projections, verify Bessel on those blocks, and identify
their prefix decomposition with the actual products (also for m>1).
-/

namespace OpenAI086

/-- A row operator may choose a different block for every row.  If the
rows form a Bessel family and the block inputs have a Bessel energy
budget, the adaptive row sum satisfies the same bound.  Neither the
rows nor the choice function need be fixed across blocks. -/
theorem finite_adaptive_row_bessel
    {n : ℕ} {Row Block : Type*}
    [Fintype Row] [Fintype Block]
    (B : Row → (Fin n → ℝ) → ℝ)
    (signal : Block → Fin n → ℝ)
    (choice : Row → Block)
    (E : ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (hblock : (∑ b : Block, finiteRealPair (signal b) (signal b)) ≤ E) :
    (∑ r : Row, (B r (signal (choice r))) ^ 2) ≤ E := by
  classical
  have hone (r : Row) :
      (∑ b : Block,
        if b = choice r then (B r (signal b)) ^ 2 else 0) =
        (B r (signal (choice r))) ^ 2 := by simp
  calc
    (∑ r : Row, (B r (signal (choice r))) ^ 2) =
        ∑ r : Row, ∑ b : Block,
          if b = choice r then (B r (signal b)) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro r _
            exact (hone r).symm
    _ = ∑ b : Block, ∑ r : Row,
          if b = choice r then (B r (signal b)) ^ 2 else 0 := by
            rw [Finset.sum_comm]
    _ ≤ ∑ b : Block, ∑ r : Row, (B r (signal b)) ^ 2 := by
          apply Finset.sum_le_sum
          intro b _
          apply Finset.sum_le_sum
          intro r _
          by_cases h : b = choice r
          · simp [h]
          · simp [h, sq_nonneg]
    _ ≤ ∑ b : Block, finiteRealPair (signal b) (signal b) := by
          apply Finset.sum_le_sum
          intro b _
          exact hrow (signal b)
    _ ≤ E := hblock

/-- Adding `K` independent Bessel-controlled levels costs at most `K²`
in squared energy (equivalently, `K` in the ℓ² norm).
This is the numerical part of the Rademacher--Menshov log argument. -/
theorem finite_level_row_square_bound
    {Row Level : Type*} [Fintype Row] [Fintype Level]
    (a : Level → Row → ℝ) (E : ℝ)
    (hlevel : ∀ k : Level, (∑ r : Row, (a k r) ^ 2) ≤ E) :
    (∑ r : Row, (∑ k : Level, a k r) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * E := by
  classical
  have hrow (r : Row) :
      (∑ k : Level, a k r) ^ 2 ≤
        (Fintype.card Level : ℝ) * (∑ k : Level, (a k r) ^ 2) := by
    have hcs := finite_row_cauchy_schwarz
      (fun k : Level => a k r) (fun _k : Level => (1 : ℝ))
    simpa [mul_comm] using hcs
  have hcard : 0 ≤ (Fintype.card Level : ℝ) := by positivity
  calc
    (∑ r : Row, (∑ k : Level, a k r) ^ 2) ≤
        ∑ r : Row, (Fintype.card Level : ℝ) *
          (∑ k : Level, (a k r) ^ 2) := by
            apply Finset.sum_le_sum
            intro r _
            exact hrow r
    _ = (Fintype.card Level : ℝ) *
        (∑ k : Level, ∑ r : Row, (a k r) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Fintype.card Level : ℝ) * (∑ _k : Level, E) := by
          apply mul_le_mul_of_nonneg_left _ hcard
          apply Finset.sum_le_sum
          intro k _
          exact hlevel k
    _ = (Fintype.card Level : ℝ) ^ 2 * E := by
          simp
          ring

/-- The adaptive row inequality over `K` families of orthogonal blocks.
The block-energy hypotheses are kept explicit so the theorem does not
smuggle in the missing dyadic-prefix decomposition. -/
theorem finite_multilevel_adaptive_row_bessel
    {n : ℕ} {Row Block Level : Type*}
    [Fintype Row] [Fintype Block] [Fintype Level]
    (B : Row → (Fin n → ℝ) → ℝ)
    (signal : Level → Block → Fin n → ℝ)
    (choice : Level → Row → Block) (E : ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (hblock : ∀ k : Level,
      (∑ b : Block, finiteRealPair (signal k b) (signal k b)) ≤ E) :
    (∑ r : Row,
        (∑ k : Level, B r (signal k (choice k r))) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * E := by
  apply finite_level_row_square_bound
    (fun k r => B r (signal k (choice k r))) E
  intro k
  exact finite_adaptive_row_bessel B (signal k) (choice k) E hrow (hblock k)

/-- Conditional form for the *actual row outputs*: it is enough to
represent each output as the sum of its chosen block contributions.
The missing work lies in constructing `signal`, `choice`, and `hdecomp`
from the nested projection families. -/
theorem finite_prefix_row_bound_from_block_decomposition
    {n : ℕ} {Row Block Level : Type*}
    [Fintype Row] [Fintype Block] [Fintype Level]
    (B : Row → (Fin n → ℝ) → ℝ)
    (signal : Level → Block → Fin n → ℝ)
    (choice : Level → Row → Block)
    (output : Row → ℝ) (E : ℝ)
    (hrow : ∀ y : Fin n → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (hblock : ∀ k : Level,
      (∑ b : Block, finiteRealPair (signal k b) (signal k b)) ≤ E)
    (hdecomp : ∀ r : Row,
      output r = ∑ k : Level, B r (signal k (choice k r))) :
    (∑ r : Row, (output r) ^ 2) ≤
      (Fintype.card Level : ℝ) ^ 2 * E := by
  calc
    (∑ r : Row, (output r) ^ 2) =
        ∑ r : Row,
          (∑ k : Level, B r (signal k (choice k r))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro r _
            rw [hdecomp r]
    _ ≤ (Fintype.card Level : ℝ) ^ 2 * E :=
          finite_multilevel_adaptive_row_bessel B signal choice E hrow hblock

end OpenAI086
