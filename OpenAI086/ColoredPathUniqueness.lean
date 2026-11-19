import Mathlib

/-!
# OpenAI #086, Lemma 9.1, p. 82: proper edge-coloring and four-step paths

The sparse-count argument uses that for a proper edge coloring, a path
with fixed starting vertex is uniquely determined by its ordered colors.
The following theorem implements precisely this statement for a length-4
path in an arbitrary bipartite graph; no uniformity, finiteness, or
additive-combinatorial estimates are assumed.

This is one small, exact combinatorial ingredient, NOT Lemma 9.1 itself.
-/

namespace OpenAI086

/-- Properness of colors for the edges incident to each vertex. -/
structure BipartiteProperColoring (U V C : Type*) where
  adjacent : U → V → Prop
  color : U → V → C
  left_unique : ∀ (u : U) (v w : V),
      adjacent u v → adjacent u w → color u v = color u w → v = w
  right_unique : ∀ (v : V) (u w : U),
      adjacent u v → adjacent w v → color u v = color w v → u = w

/-- Distinct length-four paths from one fixed start must have distinct
ordered four-color sequences. Repeated vertices are allowed. -/
theorem four_edge_colors_determine_path
    {U V C : Type*} (G : BipartiteProperColoring U V C)
    (u₀ u₂ u₄ u₂' u₄' : U) (v₁ v₃ v₁' v₃' : V)
    (h01 : G.adjacent u₀ v₁)
    (h12 : G.adjacent u₂ v₁)
    (h23 : G.adjacent u₂ v₃)
    (h34 : G.adjacent u₄ v₃)
    (h01' : G.adjacent u₀ v₁')
    (h12' : G.adjacent u₂' v₁')
    (h23' : G.adjacent u₂' v₃')
    (h34' : G.adjacent u₄' v₃')
    (hc1 : G.color u₀ v₁ = G.color u₀ v₁')
    (hc2 : G.color u₂ v₁ = G.color u₂' v₁')
    (hc3 : G.color u₂ v₃ = G.color u₂' v₃')
    (hc4 : G.color u₄ v₃ = G.color u₄' v₃') :
    v₁ = v₁' ∧ u₂ = u₂' ∧ v₃ = v₃' ∧ u₄ = u₄' := by
  have hv1 : v₁ = v₁' := G.left_unique u₀ v₁ v₁' h01 h01' hc1
  rw [← hv1] at h12' hc2
  have hu2 : u₂ = u₂' := G.right_unique v₁ u₂ u₂' h12 h12' hc2
  rw [← hu2] at h23' hc3
  have hv3 : v₃ = v₃' := G.left_unique u₂ v₃ v₃' h23 h23' hc3
  rw [← hv3] at h34' hc4
  have hu4 : u₄ = u₄' := G.right_unique v₃ u₄ u₄' h34 h34' hc4
  exact ⟨hv1, hu2, hv3, hu4⟩

end OpenAI086
