import Mathlib

/-!
# Bessel assembly on arbitrary normed spaces

Unlike the finite-real precursor, these lemmas do not depend on coordinates,
finite dimension, real-valued inputs or commutation of layers.  The codomain
of the row maps is any fixed normed additive group, so complex Hilbert spaces
are covered.  The layer Bessel and row Bessel hypotheses remain explicit:
this module is not the projection-specific statement of Lemma 3.3.
-/

namespace OpenAI086

/-- For each row, select one member of a finite Bessel family.  The
row and block Bessel hypotheses imply a bound without a row-count loss.
This is valid for any two normed additive groups. -/
theorem normed_adaptive_row_bessel
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {Row Block : Type*} [Fintype Row] [Fintype Block]
    (B : Row → X → Y) (signal : Block → X)
    (choice : Row → Block) (E : ℝ)
    (hrow : ∀ y : X, (∑ r : Row, ‖B r y‖ ^ 2) ≤ ‖y‖ ^ 2)
    (hblock : (∑ b : Block, ‖signal b‖ ^ 2) ≤ E) :
    (∑ r : Row, ‖B r (signal (choice r))‖ ^ 2) ≤ E := by
  classical
  have hone (r : Row) :
      (∑ b : Block,
        if b = choice r then ‖B r (signal b)‖ ^ 2 else 0) =
          ‖B r (signal (choice r))‖ ^ 2 := by simp
  calc
    (∑ r : Row, ‖B r (signal (choice r))‖ ^ 2) =
        ∑ r : Row, ∑ b : Block,
          if b = choice r then ‖B r (signal b)‖ ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro r _
            exact (hone r).symm
    _ = ∑ b : Block, ∑ r : Row,
          if b = choice r then ‖B r (signal b)‖ ^ 2 else 0 := by
            rw [Finset.sum_comm]
    _ ≤ ∑ b : Block, ∑ r : Row, ‖B r (signal b)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro b _
          apply Finset.sum_le_sum
          intro r _
          by_cases h : b = choice r
          · simp [h]
          · simp [h, sq_nonneg]
    _ ≤ ∑ b : Block, ‖signal b‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro b _
          exact hrow (signal b)
    _ ≤ E := hblock

/-- The first layer is applied first.  A row can choose its own block
independently at every layer; the chosen maps need not be linear or commute. -/
def normedAdaptiveWord
    {X : Type*} {Row Layer Block : Type*}
    (Q : Layer → Block → X → X) (choice : Layer → Row → Block)
    (r : Row) : List Layer → X → X
  | [], x => x
  | i :: rest, x =>
      normedAdaptiveWord Q choice r rest (Q i (choice i r) x)

/-- Dimension-free and depth-free layered Bessel assembly.  The codomain
of each row operator is a normed group, not necessarily the scalar field.
Each layer is allowed to be noncommuting and nonlinear; only its declared
Bessel energy estimate is used. -/
theorem normed_adaptive_noncommuting_row_bessel
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {Row Layer Block : Type*} [Fintype Row] [Fintype Block]
    (Q : Layer → Block → X → X)
    (choice : Layer → Row → Block)
    (hblock : ∀ i : Layer, ∀ y : X,
      (∑ b : Block, ‖Q i b y‖ ^ 2) ≤ ‖y‖ ^ 2) :
    ∀ (layers : List Layer) (B : Row → X → Y),
      (∀ y : X, (∑ r : Row, ‖B r y‖ ^ 2) ≤ ‖y‖ ^ 2) →
      ∀ x : X,
        (∑ r : Row,
          ‖B r (normedAdaptiveWord Q choice r layers x)‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  classical
  intro layers
  induction layers with
  | nil =>
      intro B hrow x
      simpa [normedAdaptiveWord] using hrow x
  | cons i rest ih =>
      intro B hrow x
      have hrest : ∀ y : X,
          (∑ r : Row,
            ‖B r (normedAdaptiveWord Q choice r rest y)‖ ^ 2) ≤
            ‖y‖ ^ 2 := by
        intro y
        exact ih B hrow y
      have hstep := normed_adaptive_row_bessel
        (fun r y => B r (normedAdaptiveWord Q choice r rest y))
        (fun b : Block => Q i b x) (choice i) (‖x‖ ^ 2)
        hrest (hblock i x)
      simpa only [normedAdaptiveWord] using hstep

/-- Full sum over all noncommuting words, now in an arbitrary normed
space.  This is the abstract Bessel iteration underlying Lemma 3.3. -/
def normedLayeredBlockEnergy
    {X : Type*} [NormedAddCommGroup X]
    {Layer Block : Type*} [Fintype Block]
    (Q : Layer → Block → X → X) : List Layer → X → ℝ
  | [], x => ‖x‖ ^ 2
  | i :: rest, x => ∑ b : Block,
      normedLayeredBlockEnergy Q rest (Q i b x)

theorem normed_noncommuting_layered_bessel
    {X : Type*} [NormedAddCommGroup X]
    {Layer Block : Type*} [Fintype Block]
    (Q : Layer → Block → X → X)
    (hblock : ∀ i : Layer, ∀ y : X,
      (∑ b : Block, ‖Q i b y‖ ^ 2) ≤ ‖y‖ ^ 2)
    (layers : List Layer) (x : X) :
    normedLayeredBlockEnergy Q layers x ≤ ‖x‖ ^ 2 := by
  classical
  induction layers generalizing x with
  | nil => exact le_rfl
  | cons i rest ih =>
      change (∑ b : Block, normedLayeredBlockEnergy Q rest (Q i b x)) ≤ ‖x‖ ^ 2
      calc
        (∑ b : Block, normedLayeredBlockEnergy Q rest (Q i b x)) ≤
            ∑ b : Block, ‖Q i b x‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro b _
              exact ih (Q i b x)
        _ ≤ ‖x‖ ^ 2 := hblock i x

end OpenAI086
