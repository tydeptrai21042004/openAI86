import Mathlib
import OpenAI086.FiniteDyadicWidthGrouping
import OpenAI086.FiniteLinearProjectionBlockBridge

/-!
# V16: constructive existence of row-dependent block/zero decisions

For each fixed dyadic width, the actual prefix grouping selects either
one aligned block or nothing. This file packages that individual
existence statement as row-indexed selection functions, requiring no
ad hoc `hdecomp`, shared row depth, or artificial coverage hypothesis.

These are *Nat*-indexed block decisions. Passing to a single bounded
`Fin count` choice family for all rows and all width tuples is a
separate, finite-indexing step needed for the V15 Bessel machinery.
-/

namespace OpenAI086

/-- For every row, choose whether its prefix contains a block of the
fixed width, and if so choose that block's aligned grid index. -/
theorem finite_dyadic_row_width_choices_exist {d : ℕ}
    {Row : Type*}
    (P : ℕ → FiniteRealEnd d)
    (N : Row → ℕ) (k width : ℕ)
    (hN : ∀ r, N r + 1 ≤ 2 ^ k) :
    ∃ (active : Row → Bool) (block : Row → ℕ),
      ∀ r : Row,
        finiteLinearWidthLevel P k 0 (N r + 1) width =
          if active r then
            finiteLinearBlock P (block r * width) width
          else 0 := by
  classical
  have hex : ∀ r : Row,
      ∃ choice : Bool × ℕ,
        finiteLinearWidthLevel P k 0 (N r + 1) width =
          if choice.1 then
            finiteLinearBlock P (choice.2 * width) width
          else 0 := by
    intro r
    rcases finite_linear_width_level_zero_or_aligned_block
      P k (N r) width (hN r) with hzero | ⟨b, hb⟩
    · exact ⟨(false, 0), by simpa using hzero⟩
    · exact ⟨(true, b), by simpa using hb⟩
  choose chooseBlock hchooseBlock using hex
  refine ⟨(fun r => (chooseBlock r).1),
    (fun r => (chooseBlock r).2), ?_⟩
  exact hchooseBlock

/-- The same fact, now evaluated as an ACTUAL projection-difference
block with the manuscript's `P₀` convention.  The block choice is
common for every test vector; it cannot depend on the input vector. -/
theorem finite_dyadic_row_paper_block_choices_exist {d : ℕ}
    {Row : Type*}
    (P : ℕ → FiniteRealEnd d)
    (N : Row → ℕ) (k width : ℕ)
    (hN : ∀ r, N r + 1 ≤ 2 ^ k) :
    ∃ (active : Row → Bool) (block : Row → ℕ),
      ∀ (r : Row) (x : Fin d → ℝ),
        (finiteLinearWidthLevel P k 0 (N r + 1) width) x =
          if active r then
            paperAlignedIncrementBlock (fun n y => P n y)
              width (block r) x
          else 0 := by
  obtain ⟨active, block, hsel⟩ :=
    finite_dyadic_row_width_choices_exist P N k width hN
  refine ⟨active, block, ?_⟩
  intro r x
  rw [hsel r]
  cases ha : active r with
  | false => simp [ha]
  | true =>
      simp only [ha, ite_true]
      exact finite_linear_block_is_projection_block
        P width (block r) x

/-- A common width chosen separately in every layer yields row-indexed
block/zero decisions for all layer-row pairs simultaneously. -/
theorem finite_dyadic_multilayer_row_choices_exist {d : ℕ}
    {Layer Row : Type*}
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Row → Layer → ℕ)
    (k : ℕ) (width : Layer → ℕ)
    (hN : ∀ r i, N r i + 1 ≤ 2 ^ k) :
    ∃ (active : Layer → Row → Bool)
      (block : Layer → Row → ℕ),
      ∀ (i : Layer) (r : Row) (x : Fin d → ℝ),
        (finiteLinearWidthLevel (P i) k 0 (N r i + 1) (width i)) x =
          if active i r then
            paperAlignedIncrementBlock (fun n y => P i n y)
              (width i) (block i r) x
          else 0 := by
  classical
  have hchoices : ∀ i : Layer,
      ∃ (active : Row → Bool) (block : Row → ℕ),
        ∀ (r : Row) (x : Fin d → ℝ),
          (finiteLinearWidthLevel (P i) k 0 (N r i + 1) (width i)) x =
            if active r then
              paperAlignedIncrementBlock (fun n y => P i n y)
                (width i) (block r) x
            else 0 := by
    intro i
    exact finite_dyadic_row_paper_block_choices_exist
      (P i) (fun r => N r i) k (width i) (fun r => hN r i)
  choose active block hselected using hchoices
  exact ⟨active, block, hselected⟩

end OpenAI086
