import Mathlib
import OpenAI086.ComponentIntersections

/-! Lemma 8.4 (p. 69): the exact primary-overlap argument.
The actual height graph and height-good stabilization (Lemma 8.3) remain
separate analytic obligations. -/
namespace OpenAI086

/-- Two predecessor sets larger than |F|/1.1 share a good primary if at
least nine tenths of the ambient primaries are good. No rounding of
cardinalities or strict thresholds is required. -/
theorem v18_good_primary_overlap {α : Type*} [DecidableEq α]
    (F A B G : Finset α) (hA : A ⊆ F) (hB : B ⊆ F) (hG : G ⊆ F)
    (ha : 10 * F.card < 11 * A.card)
    (hb : 10 * F.card < 11 * B.card)
    (hg : 9 * F.card ≤ 10 * G.card) :
    ((A ∩ B) ∩ G).Nonempty := by
  have hab := ambient_component_intersection_bound F A B hA hB
  have habsub : A ∩ B ⊆ F := by
    intro x hx
    exact hA (Finset.mem_inter.mp hx).1
  have habg := ambient_component_intersection_bound F (A ∩ B) G habsub hG
  apply Finset.card_pos.mp
  omega

/-- The coherence conclusion once a common good primary forces the two
predecessor components to coincide (the role of Lemma 8.3). -/
theorem v18_good_predecessor_coherence {α C : Type*} [DecidableEq α]
    (F A B G : Finset α) (hA : A ⊆ F) (hB : B ⊆ F) (hG : G ⊆ F)
    (ha : 10 * F.card < 11 * A.card)
    (hb : 10 * F.card < 11 * B.card)
    (hg : 9 * F.card ≤ 10 * G.card)
    (c₁ c₂ : C)
    (hjoin : ∀ p ∈ A, p ∈ B → p ∈ G → c₁ = c₂) : c₁ = c₂ := by
  obtain ⟨p, hp⟩ := v18_good_primary_overlap F A B G hA hB hG ha hb hg
  obtain ⟨hab, hgood⟩ := Finset.mem_inter.mp hp
  obtain ⟨hpa, hpb⟩ := Finset.mem_inter.mp hab
  exact hjoin p hpa hpb hgood

end OpenAI086
