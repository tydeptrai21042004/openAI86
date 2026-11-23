import Mathlib
import OpenAI086.FiniteDyadicBlockIndexBounds
import OpenAI086.FiniteDyadicRowBlockSelection

/-!
# V17: actual row-dependent width groups with bounded `Fin` choices

Each width group is either zero or a single aligned projection block.
The index is now an actual member of `Fin (2^k)` rather than an
unbounded natural number. This makes the output directly compatible
with the V15 fixed-width Bessel estimates.

Nothing in these statements depends on the test vector. They hold
simultaneously for all rows, layers, and requested widths.
-/

namespace OpenAI086

/-- A width group has one *bounded* block index or is identically zero.
When the group is present its block index lies below `2^k`; this is
proved from the input prefix geometry and not supplied as a premise. -/
theorem finite_dyadic_bounded_width_selection {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k N width : ℕ)
    (hN : N + 1 ≤ 2 ^ k) :
    ∃ (active : Bool) (block : Fin (2 ^ k)),
      ∀ x : Fin d → ℝ,
        (finiteLinearWidthLevel P k 0 (N + 1) width) x =
          if active then
            paperAlignedIncrementBlock (fun n y => P n y)
              width block.val x
          else 0 := by
  classical
  let bs := finiteDyadicPrefixBlocks k 0 (N + 1)
  by_cases hsome : ∃ b : ℕ × ℕ, b ∈ bs ∧ b.2 = width
  · obtain ⟨b, hb, hw⟩ := hsome
    have halign : b.2 ∣ b.1 :=
      finite_dyadic_zero_base_blocks_aligned k (N + 1) hN b hb
    obtain ⟨index, hindex⟩ := halign
    have hsmall : index < 2 ^ k := by
      apply finite_dyadic_aligned_block_index_lt k (N + 1) hN b hb index
      simpa [Nat.mul_comm] using hindex
    refine ⟨true, ⟨index, hsmall⟩, ?_⟩
    intro x
    have heq := finite_linear_width_level_of_member
      P k 0 (N + 1) hN b hb
    simp only [ite_true]
    rw [heq]
    have hindex' : b.1 = index * width := by
      simpa [hw, Nat.mul_comm] using hindex
    rw [hindex', hw]
    exact finite_linear_block_is_projection_block P width index x
  · have hnot : width ∉ (bs.map Prod.snd) := by
      intro hm
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
      exact hsome ⟨b, hb, heq⟩
    have hz : finiteLinearWidthLevel P k 0 (N + 1) width = 0 := by
      apply grouped_linear_list_zero_of_absent
      simpa [finiteDyadicLinearPairs, List.map_map, Function.comp_def]
        using hnot
    have hpos : 0 < 2 ^ k := by positivity
    refine ⟨false, ⟨0, hpos⟩, ?_⟩
    intro x
    simp [hz]

/-- A bounded block/zero decision can be chosen simultaneously for
all rows of an arbitrary (possibly empty) row type. -/
theorem finite_dyadic_bounded_row_choices {d : ℕ} {Row : Type*}
    (P : ℕ → FiniteRealEnd d) (N : Row → ℕ)
    (k width : ℕ) (hN : ∀ r, N r + 1 ≤ 2 ^ k) :
    ∃ (active : Row → Bool) (block : Row → Fin (2 ^ k)),
      ∀ (r : Row) (x : Fin d → ℝ),
        (finiteLinearWidthLevel P k 0 (N r + 1) width) x =
          if active r then
            paperAlignedIncrementBlock (fun n y => P n y)
              width (block r).val x
          else 0 := by
  classical
  have hex : ∀ r : Row,
      ∃ c : Bool × Fin (2 ^ k), ∀ x : Fin d → ℝ,
        (finiteLinearWidthLevel P k 0 (N r + 1) width) x =
          if c.1 then paperAlignedIncrementBlock
            (fun n y => P n y) width c.2.val x else 0 := by
    intro r
    obtain ⟨active, block, hblock⟩ :=
      finite_dyadic_bounded_width_selection P k (N r) width (hN r)
    exact ⟨(active, block), hblock⟩
  choose selected hselected using hex
  exact ⟨(fun r => (selected r).1), (fun r => (selected r).2), hselected⟩

/-- Multiple potentially noncommuting families: the same finite block
budget works for every row, layer and requested width tuple. -/
theorem finite_dyadic_bounded_multilayer_choices {d : ℕ}
    {Layer Row : Type*}
    (P : Layer → ℕ → FiniteRealEnd d)
    (N : Row → Layer → ℕ)
    (k : ℕ) (width : Layer → ℕ)
    (hN : ∀ r i, N r i + 1 ≤ 2 ^ k) :
    ∃ (active : Layer → Row → Bool)
      (block : Layer → Row → Fin (2 ^ k)),
      ∀ (i : Layer) (r : Row) (x : Fin d → ℝ),
        (finiteLinearWidthLevel (P i) k 0 (N r i + 1)
          (width i)) x =
          if active i r then
            paperAlignedIncrementBlock (fun n y => P i n y)
              (width i) (block i r).val x
          else 0 := by
  classical
  have hs : ∀ i : Layer,
      ∃ (a : Row → Bool) (b : Row → Fin (2 ^ k)),
        ∀ (r : Row) (x : Fin d → ℝ),
          (finiteLinearWidthLevel (P i) k 0 (N r i + 1)
            (width i)) x =
            if a r then paperAlignedIncrementBlock
              (fun n y => P i n y) (width i) (b r).val x else 0 := by
    intro i
    exact finite_dyadic_bounded_row_choices (P i) (fun r => N r i)
      k (width i) (fun r => hN r i)
  choose a b hab using hs
  exact ⟨a, b, hab⟩

end OpenAI086
