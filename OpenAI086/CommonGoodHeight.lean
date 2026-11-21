import Mathlib

/-!
# Section 9.1: a positive proportion of common good heights

For a tuple of up to four core modes, the paper selects a height at
which *every role* passes its good-height predicate. The relevant
finite-set union bound is made explicit here in the four-role case.

Each role is permitted to be bad on at most one eighth of the sampled
heights; at least half the heights are then simultaneously good. This
is the deterministic counting fact underlying the positive success
probability in the subsequent randomized height selection.

This module does not formalize independent random sampling, the fixed
mode expansion, or the Section 9 sparse counting theorem.
-/

namespace OpenAI086

/-- The complement of four bad-height sets has at least half of the
ambient cardinality, provided each bad set occupies at most one eighth. -/
theorem four_roles_common_good_at_least_half
    {α : Type*} [DecidableEq α]
    (heights B₀ B₁ B₂ B₃ : Finset α)
    (h₀ : 8 * B₀.card ≤ heights.card)
    (h₁ : 8 * B₁.card ≤ heights.card)
    (h₂ : 8 * B₂.card ≤ heights.card)
    (h₃ : 8 * B₃.card ≤ heights.card) :
    heights.card ≤ 2 * (heights \ (B₀ ∪ B₁ ∪ B₂ ∪ B₃)).card := by
  let U := B₀ ∪ B₁ ∪ B₂ ∪ B₃
  have hcover : heights ⊆ (heights \ U) ∪ U := by
    intro x hx
    by_cases hU : x ∈ U
    · exact Finset.mem_union.mpr (Or.inr hU)
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hU⟩))
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (heights \ U) U
  have h01 := Finset.card_union_le B₀ B₁
  have h012 := Finset.card_union_le (B₀ ∪ B₁) B₂
  have h0123 := Finset.card_union_le (B₀ ∪ B₁ ∪ B₂) B₃
  dsimp [U] at hc hu
  omega

/-- If the ambient height set is nonempty, there exists at least one
height good for all four roles under the same density assumptions. -/
theorem four_roles_have_common_good_height
    {α : Type*} [DecidableEq α]
    (heights B₀ B₁ B₂ B₃ : Finset α)
    (hpos : 0 < heights.card)
    (h₀ : 8 * B₀.card ≤ heights.card)
    (h₁ : 8 * B₁.card ≤ heights.card)
    (h₂ : 8 * B₂.card ≤ heights.card)
    (h₃ : 8 * B₃.card ≤ heights.card) :
    ∃ x ∈ heights, x ∉ B₀ ∧ x ∉ B₁ ∧ x ∉ B₂ ∧ x ∉ B₃ := by
  have h := four_roles_common_good_at_least_half
    heights B₀ B₁ B₂ B₃ h₀ h₁ h₂ h₃
  have hcardpos : 0 < (heights \ (B₀ ∪ B₁ ∪ B₂ ∪ B₃)).card := by
    omega
  have hne : (heights \ (B₀ ∪ B₁ ∪ B₂ ∪ B₃)).Nonempty :=
    Finset.card_pos.mp hcardpos
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxH, hxBad⟩ := Finset.mem_sdiff.mp hx
  have hx0 : x ∉ B₀ := by
    intro h0
    exact hxBad (by simp [h0])
  have hx1 : x ∉ B₁ := by
    intro h1
    exact hxBad (by simp [h1])
  have hx2 : x ∉ B₂ := by
    intro h2
    exact hxBad (by simp [h2])
  have hx3 : x ∉ B₃ := by
    intro h3
    exact hxBad (by simp [h3])
  exact ⟨x, hxH, hx0, hx1, hx2, hx3⟩

end OpenAI086
