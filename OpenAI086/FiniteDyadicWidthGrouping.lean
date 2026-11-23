import Mathlib
import OpenAI086.FiniteLinearDyadicExpansion
import OpenAI086.FiniteDyadicDistinctLengths

/-!
# V16: unconditional grouping of a dyadic prefix by common widths

The row-dependent prefix partition from `finiteDyadicPrefixBlocks` is a
list.  Different rows may have different list lengths and block positions.
For the Hilbert-space argument in Lemma 3.3 the level must instead be
its *width*: all rows must share the same set of width labels, while their
block positions are allowed to differ.

This file provides the algebraic change of indexing. It does not use an
assumed Bessel inequality, an assumed `hdecomp`, or commutativity.
The *analytic* row-Bessel estimate for the resulting width groups is a
separate obligation; successful kernel compilation is also required.
-/

namespace OpenAI086

/-- Group any finite list of additive operators by a common numerical
label; the original list need not be sorted or injective. -/
def groupedLinearList {d : ℕ}
    (blocks : List (ℕ × FiniteRealEnd d)) (label : ℕ) : FiniteRealEnd d :=
  (blocks.map (fun p => if p.1 = label then p.2 else 0)).sum

/-- Regrouping is an exact equality, not an estimate.  This general
statement is also useful outside the specific dyadic construction. -/
theorem grouped_linear_list_sum {d : ℕ}
    (labels : Finset ℕ) (blocks : List (ℕ × FiniteRealEnd d))
    (hsupport : ∀ p ∈ blocks, p.1 ∈ labels) :
    (∑ w ∈ labels, groupedLinearList blocks w) =
      (blocks.map Prod.snd).sum := by
  classical
  induction blocks with
  | nil => simp [groupedLinearList]
  | cons p rest ih =>
      obtain ⟨w, F⟩ := p
      have hw : w ∈ labels := hsupport (w, F) (by simp)
      have hrest : ∀ q ∈ rest, q.1 ∈ labels := by
        intro q hq
        exact hsupport q (by simp [hq])
      have ih' := ih hrest
      simp only [groupedLinearList, List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib]
      have hsingle :
          (∑ t ∈ labels, if w = t then F else (0 : FiniteRealEnd d)) = F := by
        simp [hw]
      rw [hsingle]
      exact congrArg (fun z : FiniteRealEnd d => F + z) ih'

/-- The common width set is fixed once `k` is chosen and is independent
of the row or of its prefix depth. Its cardinality is at most `k+1`. -/
def finiteDyadicWidthSet (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).image (fun j : ℕ => 2 ^ j)

theorem finite_dyadic_width_mem_set (k start length : ℕ)
    (hlen : length ≤ 2 ^ k) (b : ℕ × ℕ)
    (hb : b ∈ finiteDyadicPrefixBlocks k start length) :
    b.2 ∈ finiteDyadicWidthSet k := by
  obtain ⟨j, hj, hwidth⟩ :=
    finite_dyadic_width_is_power_two k start length hlen b hb
  exact Finset.mem_image.mpr
    ⟨j, Finset.mem_range.mpr (by omega), hwidth.symm⟩

theorem finite_dyadic_width_set_card_le (k : ℕ) :
    (finiteDyadicWidthSet k).card ≤ k + 1 := by
  unfold finiteDyadicWidthSet
  calc
    ((Finset.range (k + 1)).image (fun j : ℕ => 2 ^ j)).card ≤
        (Finset.range (k + 1)).card := Finset.card_image_le
    _ = k + 1 := Finset.card_range _

/-- Attach each block's *width*, not its position in the returned list,
as a label for exact level-wise summation. -/
def finiteDyadicLinearPairs {d : ℕ} (P : ℕ → FiniteRealEnd d)
    (k start length : ℕ) : List (ℕ × FiniteRealEnd d) :=
  (finiteDyadicPrefixBlocks k start length).map
    (fun b => (b.2, finiteLinearBlock P b.1 b.2))

/-- A width group uses only blocks of that width; the same width set
works for every row's chosen prefix. -/
def finiteLinearWidthLevel {d : ℕ} (P : ℕ → FiniteRealEnd d)
    (k start length width : ℕ) : FiniteRealEnd d :=
  groupedLinearList (finiteDyadicLinearPairs P k start length) width

/-- Convert the original recursive block-list sum to an ordinary list
sum, independent of the order in which one later groups the terms. -/
theorem finite_linear_block_list_eq_sum {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (blocks : List (ℕ × ℕ)) :
    finiteLinearBlockList P blocks =
      (blocks.map (fun b => finiteLinearBlock P b.1 b.2)).sum := by
  induction blocks with
  | nil => simp [finiteLinearBlockList]
  | cons b rest ih =>
      obtain ⟨s, w⟩ := b
      simp [finiteLinearBlockList, ih]

/-- Unconditional exact operator identity for a row-dependent prefix,
with its blocks indexed by a COMMON finite width set.

No input-vector restriction, projection assumption, row-map assumption,
or commuting relation is used.  This replaces the single-family
``hlevels`` padding premise in the older V7 bridge. -/
theorem finite_linear_prefix_grouped_by_width {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k N : ℕ)
    (hN : N + 1 ≤ 2 ^ k) :
    (∑ w ∈ finiteDyadicWidthSet k,
      finiteLinearWidthLevel P k 0 (N + 1) w) = P N := by
  have hsupport :
      ∀ p ∈ finiteDyadicLinearPairs P k 0 (N + 1),
        p.1 ∈ finiteDyadicWidthSet k := by
    intro p hp
    simp only [finiteDyadicLinearPairs, List.mem_map] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    exact finite_dyadic_width_mem_set k 0 (N + 1) hN b hb
  have hgroup := grouped_linear_list_sum
    (finiteDyadicWidthSet k)
    (finiteDyadicLinearPairs P k 0 (N + 1)) hsupport
  calc
    (∑ w ∈ finiteDyadicWidthSet k,
      finiteLinearWidthLevel P k 0 (N + 1) w) =
        ((finiteDyadicPrefixBlocks k 0 (N + 1)).map
          (fun b => finiteLinearBlock P b.1 b.2)).sum := by
            simpa [finiteLinearWidthLevel, finiteDyadicLinearPairs,
              List.map_map, Function.comp_def] using hgroup
    _ = finiteLinearBlockList P
        (finiteDyadicPrefixBlocks k 0 (N + 1)) :=
          (finite_linear_block_list_eq_sum P _).symm
    _ = P N := finite_linear_operator_dyadic_prefix P k N hN


/-- The common-width grouping never hides multiple blocks of the same
width in one row. This is a constructive consequence of the prefix
algorithm, and is essential before applying fixed-width Bessel bounds. -/
theorem finite_dyadic_linear_pairs_widths_nodup {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k start length : ℕ)
    (hlen : length ≤ 2 ^ k) :
    ((finiteDyadicLinearPairs P k start length).map Prod.fst).Nodup := by
  simpa [finiteDyadicLinearPairs, List.map_map, Function.comp_def] using
    (finite_dyadic_prefix_widths_nodup k start length hlen)

/-- The grouped operator at a width absent from the list is exactly zero,
not an unknown vector or an extra hypothetical projection block. -/
theorem grouped_linear_list_zero_of_absent {d : ℕ}
    (pairs : List (ℕ × FiniteRealEnd d)) (w : ℕ)
    (habsent : w ∉ pairs.map Prod.fst) :
    groupedLinearList pairs w = 0 := by
  induction pairs with
  | nil => simp [groupedLinearList]
  | cons p rest ih =>
      obtain ⟨v, F⟩ := p
      have hv : v ≠ w := by
        intro h
        apply habsent
        simp [h]
      have htail : w ∉ rest.map Prod.fst := by
        intro h
        apply habsent
        simp [h]
      simp [groupedLinearList, hv, ih htail]

/-- At base `0`, every block has an actual aligned integer-grid
position. This is the second hypothesis needed for the projection
block-energy estimate at a fixed dyadic width. -/
theorem finite_dyadic_zero_base_blocks_aligned
    (k length : ℕ) (hlen : length ≤ 2 ^ k)
    (b : ℕ × ℕ) (hb : b ∈ finiteDyadicPrefixBlocks k 0 length) :
    b.2 ∣ b.1 := by
  exact finite_dyadic_prefix_block_aligned
    k 0 length hlen (dvd_zero _) b hb


/-- If the labels occur at most once, the grouped contribution at a
present label is exactly its single associated operator. -/
theorem grouped_linear_list_of_unique {d : ℕ} :
    ∀ (pairs : List (ℕ × FiniteRealEnd d)) (w : ℕ)
      (F : FiniteRealEnd d),
      (w, F) ∈ pairs → (pairs.map Prod.fst).Nodup →
      groupedLinearList pairs w = F := by
  intro pairs
  induction pairs with
  | nil =>
      intro w F hmem _
      simp at hmem
  | cons p ps ih =>
      intro w F hmem hnodup
      have hcons : (p.1 :: ps.map Prod.fst).Nodup := by
        simpa using hnodup
      obtain ⟨habsent, htailnodup⟩ := List.nodup_cons.mp hcons
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        have hz := grouped_linear_list_zero_of_absent ps w habsent
        change (if w = w then F else 0) + groupedLinearList ps w = F
        simp [hz]
      · have hneq : p.1 ≠ w := by
          intro heq
          apply habsent
          have hw : w ∈ ps.map Prod.fst := by
            exact List.mem_map.mpr ⟨(w, F), htail, rfl⟩
          simpa [heq] using hw
        change (if p.1 = w then p.2 else 0) +
          groupedLinearList ps w = F
        simp [hneq, ih w F htail htailnodup]

/-- Selecting a known block from the prefix's width-indexed operator
sum yields exactly that block, with no sum of unrelated same-width terms. -/
theorem finite_linear_width_level_of_member {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k start length : ℕ)
    (hlen : length ≤ 2 ^ k) (b : ℕ × ℕ)
    (hb : b ∈ finiteDyadicPrefixBlocks k start length) :
    finiteLinearWidthLevel P k start length b.2 =
      finiteLinearBlock P b.1 b.2 := by
  unfold finiteLinearWidthLevel
  apply grouped_linear_list_of_unique
  · exact List.mem_map.mpr ⟨b, hb, rfl⟩
  · exact finite_dyadic_linear_pairs_widths_nodup P k start length hlen

/-- A fixed width contributes either zero or exactly ONE aligned
operator-increment block, depending on the row's selected prefix.
This is the precise singleton-or-zero property used in the paper's
fixed-width Bessel grouping, and it does not assume that grouping as an
axiom. -/
theorem finite_linear_width_level_zero_or_aligned_block {d : ℕ}
    (P : ℕ → FiniteRealEnd d) (k N width : ℕ)
    (hN : N + 1 ≤ 2 ^ k) :
    finiteLinearWidthLevel P k 0 (N + 1) width = 0 ∨
      ∃ block : ℕ,
        finiteLinearWidthLevel P k 0 (N + 1) width =
          finiteLinearBlock P (block * width) width := by
  let bs := finiteDyadicPrefixBlocks k 0 (N + 1)
  by_cases hsome : ∃ b : ℕ × ℕ, b ∈ bs ∧ b.2 = width
  · obtain ⟨b, hb, hw⟩ := hsome
    have halign : b.2 ∣ b.1 :=
      finite_dyadic_zero_base_blocks_aligned k (N + 1) hN b hb
    obtain ⟨block, hblock⟩ := halign
    right
    refine ⟨block, ?_⟩
    have heq := finite_linear_width_level_of_member
      P k 0 (N + 1) hN b hb
    simpa [hw, hblock, Nat.mul_comm] using heq
  · left
    have hnot : width ∉ (bs.map Prod.snd) := by
      intro hh
      obtain ⟨b, hb, hbwidth⟩ := List.mem_map.mp hh
      exact hsome ⟨b, hb, hbwidth⟩
    apply grouped_linear_list_zero_of_absent
    simpa [finiteDyadicLinearPairs, List.map_map, Function.comp_def]
      using hnot

end OpenAI086
