import Mathlib

/-!
# OpenAI #086, Lemma 3.3: algebra of ordered, noncommuting products

This is an original, exact proof of the telescoping identity used in the
second part of Lemma 3.3.  The endomorphisms need NOT commute.  It does not
prove the Rademacher--Menshov square-function estimate or all of Lemma 3.3.
-/

namespace OpenAI086

/-- The three-layer ordered telescoping formula.  Its order is crucial:
new operators appear on the left; old operators appear on the right. -/
theorem ordered_telescoping_three
    {E : Type*} [AddCommGroup E]
    (P₁ P₂ P₃ Q₁ Q₂ Q₃ : E →+ E) (z : E) :
    P₃ (P₂ (P₁ z)) - Q₃ (Q₂ (Q₁ z)) =
      P₃ (P₂ (P₁ z - Q₁ z)) +
      P₃ (P₂ (Q₁ z) - Q₂ (Q₁ z)) +
      (P₃ (Q₂ (Q₁ z)) - Q₃ (Q₂ (Q₁ z))) := by
  simp only [map_sub]
  abel

/-- A four-layer ordered telescoping formula for arbitrary additive
endomorphisms. No pair of endomorphisms is assumed to commute. -/
theorem ordered_telescoping_four
    {E : Type*} [AddCommGroup E]
    (P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : E →+ E) (z : E) :
    P₄ (P₃ (P₂ (P₁ z))) - Q₄ (Q₃ (Q₂ (Q₁ z))) =
      P₄ (P₃ (P₂ (P₁ z - Q₁ z))) +
      P₄ (P₃ (P₂ (Q₁ z) - Q₂ (Q₁ z))) +
      P₄ (P₃ (Q₂ (Q₁ z)) - Q₃ (Q₂ (Q₁ z))) +
      (P₄ (Q₃ (Q₂ (Q₁ z))) - Q₄ (Q₃ (Q₂ (Q₁ z)))) := by
  simp only [map_sub]
  abel

end OpenAI086
