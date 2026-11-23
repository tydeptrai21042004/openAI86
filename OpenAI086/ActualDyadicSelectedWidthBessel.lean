import Mathlib
import OpenAI086.FiniteDyadicBoundedRowSelection
import OpenAI086.ActualDyadicTupleBessel
import OpenAI086.ActualDyadicMaskedLevelSum

/-!
# V17: the row-prefix Bessel bound at one actual dyadic width

This lemma eliminates the `hchoice` and `hmask` premises for ONE width.
For every row r, the prefix P_(N r) is formed using actual nested
projections; the binary-prefix algorithm picks zero or a single
aligned increment. The resulting fixed-width row family has exact
Bessel constant one, regardless of how the row depths vary.

The full logarithmic inequality also needs a finite assembly over all
width tuples and a separate argument for the square-variation bound.
-/

namespace OpenAI086

/-- Unconditional fixed-width Bessel inequality for actual row-specific
prefix decompositions, with no assumed block selector, and with the
row maps explicitly LINEAR (as required in manuscript Lemma 3.3). -/
theorem actual_dyadic_selected_width_row_bessel
    {d : ℕ} {Row : Type*} [Fintype Row]
    (P : ℕ → FiniteRealEnd d)
    (hsym : ∀ j u v,
      finiteRealPair (P j u) v = finiteRealPair u (P j v))
    (hidemp : ∀ j u, P j (P j u) = P j u)
    (hnested : ∀ j u, P j (P (j + 1) u) = P j u)
    (N : Row → ℕ) (k width : ℕ)
    (hN : ∀ r, N r + 1 ≤ 2 ^ k)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row,
      (B r ((finiteLinearWidthLevel P k 0 (N r + 1) width) x)) ^ 2)
      ≤ finiteRealPair x x := by
  classical
  obtain ⟨active, block, hselected⟩ :=
    finite_dyadic_bounded_row_choices P N k width hN
  have hmasked : ∀ y : Fin d → ℝ,
      (∑ r : Row, (if active r then B r y else 0) ^ 2) ≤
        finiteRealPair y y :=
    masked_finite_row_contraction (fun r y => B r y) hrow active
  have h := actual_dyadic_one_layer_adaptive_bessel P
    hsym hidemp hnested width block
    (fun r y => if active r then B r y else 0) hmasked x
  calc
    (∑ r : Row,
      (B r ((finiteLinearWidthLevel P k 0 (N r + 1) width) x)) ^ 2) =
      (∑ r : Row,
        (if active r then
          B r (paperAlignedIncrementBlock
            (fun n y => P n y) width (block r).val x)
        else 0) ^ 2) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hselected r x]
          cases ha : active r with
          | false => simp [ha]
          | true => simp [ha]
    _ ≤ finiteRealPair x x := h

end OpenAI086
