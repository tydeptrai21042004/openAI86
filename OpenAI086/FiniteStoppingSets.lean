import Mathlib

/-!
# OpenAI #086, Lemma 2.4: finite union of four exceptional sets

This proves a genuine finite-set counterpart of the paper's union-of-stops
estimate. The real proof uses measure, dyadic stopping times, and a maximal
function; those analytic elements are not inferred from a cardinality model.
-/

namespace OpenAI086

/-- Four exceptional sets of size at most `|root|/16` have a union of
size at most `|root|/4`, even when they overlap. -/
theorem four_finite_stop_union_bound
    {α : Type*} [DecidableEq α]
    (root S₀ S₁ S₂ S₃ : Finset α)
    (h₀ : 16 * S₀.card ≤ root.card)
    (h₁ : 16 * S₁.card ≤ root.card)
    (h₂ : 16 * S₂.card ≤ root.card)
    (h₃ : 16 * S₃.card ≤ root.card) :
    4 * (S₀ ∪ S₁ ∪ S₂ ∪ S₃).card ≤ root.card := by
  have h01 := Finset.card_union_le S₀ S₁
  have h012 := Finset.card_union_le (S₀ ∪ S₁) S₂
  have h0123 := Finset.card_union_le (S₀ ∪ S₁ ∪ S₂) S₃
  omega

end OpenAI086
