import Mathlib
import OpenAI086.GeneralNestedProjectionEnergy

/-!
# Lemma 3.3: Bessel estimates for arbitrarily many noncommuting layers

Every layer may consist of an arbitrary finite family of (not
necessarily commuting) operators whose **total squared energy** is
contractive.  Every word of chosen blocks is applied in a prescribed
order; summing the energies of *all* words is still contractive.

This is exactly the repeated-Bessel step in the paper's binary-block
proof, with an arbitrary number of layers. No commutativity across
layers, nor an a priori factor `|Block|^m`, is introduced.

The actual construction of the dyadic block operators from nested
orthogonal projections, the row grouping, and logarithmic sum over
block lengths are distinct steps.  Thus this is a substantive
intermediate theorem, not a proof of all of Lemma 3.3.
-/

namespace OpenAI086

/-- Squared energy of all noncommutative block words along a fixed
ordered list of projection families.  A word chooses one block at
each layer; the selected operators are applied from the list's head
toward its tail. -/
def layeredBlockEnergy
    {n : ℕ} {Layer Block : Type*} [Fintype Block]
    (Q : Layer → Block → (Fin n → ℝ) → (Fin n → ℝ)) :
    List Layer → (Fin n → ℝ) → ℝ
  | [], x => finiteRealPair x x
  | i :: rest, x => ∑ b : Block,
      layeredBlockEnergy Q rest (Q i b x)

/-- **General noncommuting-layer Bessel inequality.** Each layer is
allowed to be different; after `m` layers the total squared energy
of *all* selected products is at most the original energy, with
bound of one, independent of `m` and of the block count. -/
theorem noncommuting_layered_bessel
    {n : ℕ} {Layer Block : Type*} [Fintype Block]
    (Q : Layer → Block → (Fin n → ℝ) → (Fin n → ℝ))
    (hBessel : ∀ i : Layer, ∀ x : Fin n → ℝ,
      (∑ b : Block, finiteRealPair (Q i b x) (Q i b x)) ≤
        finiteRealPair x x)
    (layers : List Layer) (x : Fin n → ℝ) :
    layeredBlockEnergy Q layers x ≤ finiteRealPair x x := by
  classical
  induction layers generalizing x with
  | nil =>
      exact le_rfl
  | cons i rest ih =>
      change (∑ b : Block, layeredBlockEnergy Q rest (Q i b x)) ≤
        finiteRealPair x x
      calc
        (∑ b : Block, layeredBlockEnergy Q rest (Q i b x)) ≤
            ∑ b : Block, finiteRealPair (Q i b x) (Q i b x) := by
              apply Finset.sum_le_sum
              intro b _
              exact ih (Q i b x)
        _ ≤ finiteRealPair x x := hBessel i x

/-- Two concrete noncommuting layers are covered without a pairwise
commutation hypothesis. This version makes the precise energy
ordering explicit and can be used before introducing a list API. -/
theorem noncommuting_two_layer_bessel
    {n : ℕ} {Block : Type*} [Fintype Block]
    (Q R : Block → (Fin n → ℝ) → (Fin n → ℝ))
    (hQ : ∀ x : Fin n → ℝ,
      (∑ b : Block, finiteRealPair (Q b x) (Q b x)) ≤
        finiteRealPair x x)
    (hR : ∀ x : Fin n → ℝ,
      (∑ b : Block, finiteRealPair (R b x) (R b x)) ≤
        finiteRealPair x x)
    (x : Fin n → ℝ) :
    (∑ b : Block, ∑ c : Block,
        finiteRealPair (R c (Q b x)) (R c (Q b x))) ≤
      finiteRealPair x x := by
  classical
  calc
    (∑ b : Block, ∑ c : Block,
        finiteRealPair (R c (Q b x)) (R c (Q b x))) ≤
      ∑ b : Block, finiteRealPair (Q b x) (Q b x) := by
        apply Finset.sum_le_sum
        intro b _
        exact hR (Q b x)
    _ ≤ finiteRealPair x x := hQ x

end OpenAI086
