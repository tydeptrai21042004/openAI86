import Mathlib
import OpenAI086.FiniteLinearDyadicExpansion

/-!
# Exact expansion of noncommuting linear-map products

For each layer i, suppose its operator is a finite sum of blocks.
An arbitrarily long ordered product of those layer operators is exactly
the nested finite sum over all selected block products. The order of
layers is preserved; no assumption of pairwise commutativity is used.

This discharges the purely ALGEBRAIC multi-family distributivity part of
the `hdecomp` obligation identified in V5/V6 for manuscript Lemma 3.3.
The indexing of actual dyadic length tuples and the logarithmic Bessel
bounds remain separate open obligations.
-/

namespace OpenAI086

/-- First list element is applied first, preserving noncommutative
composition order. -/
def finiteOrderedLinearProduct {d : ℕ} {Layer : Type*}
    (P : Layer → FiniteRealEnd d) : List Layer → FiniteRealEnd d
  | [] => LinearMap.id
  | i :: rest => (finiteOrderedLinearProduct P rest).comp (P i)

/-- Expand each chosen layer into blocks, retaining the *original*
composition order. -/
def finiteExpandedLinearProduct {d : ℕ}
    {Layer Block : Type*} [Fintype Block]
    (Q : Layer → Block → FiniteRealEnd d) :
    List Layer → FiniteRealEnd d
  | [] => LinearMap.id
  | i :: rest => ∑ b : Block,
      (finiteExpandedLinearProduct Q rest).comp (Q i b)

/-- Full ordered distributivity across an arbitrary number of
noncommuting layers. No projection assumptions are needed, only linearity
(and a true operator-level sum identity at each layer). -/
theorem finite_ordered_product_expansion {d : ℕ}
    {Layer Block : Type*} [Fintype Block]
    (P : Layer → FiniteRealEnd d)
    (Q : Layer → Block → FiniteRealEnd d)
    (hsum : ∀ i : Layer, P i = ∑ b : Block, Q i b)
    (layers : List Layer) :
    finiteOrderedLinearProduct P layers =
      finiteExpandedLinearProduct Q layers := by
  classical
  induction layers with
  | nil => rfl
  | cons i rest ih =>
      apply LinearMap.ext
      intro x
      change (finiteOrderedLinearProduct P rest) (P i x) =
        (∑ b : Block,
          (finiteExpandedLinearProduct Q rest).comp (Q i b)) x
      rw [ih, hsum i]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      exact map_sum (finiteExpandedLinearProduct Q rest)
        (fun b : Block => (Q i b) x) Finset.univ

/-- Two layers are a useful concrete corollary: if the two original
operators are sums, the output is a sum of noncommuting ordered
block-products. -/
theorem finite_two_layer_ordered_expansion {d : ℕ}
    {Block : Type*} [Fintype Block]
    (A B : Block → FiniteRealEnd d) :
    ((∑ b : Block, B b).comp (∑ a : Block, A a)) =
      ∑ a : Block, ∑ b : Block, (B b).comp (A a) := by
  classical
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  simp only [map_sum]
  rw [Finset.sum_comm]

/-- Specialization to the *actual* finite dyadic decomposition of
one (or many) linear-map prefixes. The only remaining input is a common
finite block type and a per-layer operator identity; no artificial
commutativity hypothesis enters. -/
theorem finite_product_from_layer_block_sums {d : ℕ}
    {Layer Block : Type*} [Fintype Block]
    (P : Layer → FiniteRealEnd d)
    (block : Layer → Block → FiniteRealEnd d)
    (hblock : ∀ i : Layer, P i = ∑ b : Block, block i b)
    (layers : List Layer) (x : Fin d → ℝ) :
    (finiteOrderedLinearProduct P layers) x =
      (finiteExpandedLinearProduct block layers) x := by
  exact congrArg (fun F : FiniteRealEnd d => F x)
    (finite_ordered_product_expansion P block hblock layers)

end OpenAI086
