import Mathlib
import OpenAI086.FiniteLinearDyadicExpansion
import OpenAI086.FiniteOrderedProductExpansion

/-!
# Connecting dyadic prefix lists to noncommutative ordered products

The first theorem is unconditional: if each layer is a genuine real
linear map, an arbitrary ordered product of possibly distinct prefix
operators equals the ordered product of their exact dyadic block lists.
No commutativity is needed.

The second theorem identifies the *remaining* uniform finite-index
representation obligation for the analytic row-prefix proof. The
hypothesis `hlevels` must eventually be constructed from the dyadic
block algorithm and cannot be assumed when claiming Lemma 3.3.
-/

namespace OpenAI086

/-- Direct multi-family dyadic replacement, with the paper's convention
that a prefix of length `N+1` includes the initial increment `P₀`. -/
theorem finite_ordered_dyadic_prefix_replacement {d : ℕ}
    {Layer : Type*}
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Layer → ℕ) (k : ℕ)
    (hN : ∀ i, N i + 1 ≤ 2 ^ k)
    (layers : List Layer) :
    finiteOrderedLinearProduct (fun i => P i (N i)) layers =
      finiteOrderedLinearProduct
        (fun i => finiteLinearBlockList (P i)
          (finiteDyadicPrefixBlocks k 0 (N i + 1))) layers := by
  have heq : (fun i => P i (N i)) =
      (fun i => finiteLinearBlockList (P i)
        (finiteDyadicPrefixBlocks k 0 (N i + 1))) := by
    funext i
    exact (finite_linear_operator_dyadic_prefix
      (P i) k (N i) (hN i)).symm
  exact congrArg (fun F : Layer → FiniteRealEnd d =>
    finiteOrderedLinearProduct F layers) heq

/-- Exact ordered block expansion conditional only on a genuine
per-layer uniform finite-index sum. The new hypothesis is a precise
combinatorial padding problem, NOT the target logarithmic inequality.
Its construction, Hilbert Bessel bounds, and square variation are open. -/
theorem finite_ordered_dyadic_level_expansion {d : ℕ}
    {Layer Level : Type*} [Fintype Level]
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Layer → ℕ) (k : ℕ)
    (hN : ∀ i, N i + 1 ≤ 2 ^ k)
    (Q : Layer → Level → FiniteRealEnd d)
    (hlevels : ∀ i : Layer,
      finiteLinearBlockList (P i)
        (finiteDyadicPrefixBlocks k 0 (N i + 1)) =
        ∑ b : Level, Q i b)
    (layers : List Layer) :
    finiteOrderedLinearProduct (fun i => P i (N i)) layers =
      finiteExpandedLinearProduct Q layers := by
  calc
    finiteOrderedLinearProduct (fun i => P i (N i)) layers =
        finiteOrderedLinearProduct
          (fun i => finiteLinearBlockList (P i)
            (finiteDyadicPrefixBlocks k 0 (N i + 1))) layers :=
          finite_ordered_dyadic_prefix_replacement P N k hN layers
    _ = finiteExpandedLinearProduct Q layers :=
          finite_ordered_product_expansion
            (fun i => finiteLinearBlockList (P i)
              (finiteDyadicPrefixBlocks k 0 (N i + 1))) Q hlevels layers

end OpenAI086
