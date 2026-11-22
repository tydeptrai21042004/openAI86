import Mathlib
import OpenAI086.ColoredPathUniqueness

/-!
# Arbitrary-length properly colored alternating paths (Lemma 9.1)

The combinatorial proof on manuscript page 83 needs that the ordered
color sequence reconstructs a path from a prescribed start vertex.
`ColoredPathUniqueness` formalizes length four. We generalize that
argument independently to **every finite even length**, allowing
repeated vertices and without adding injectivity assumptions beyond
proper edge coloring. This proves path-code uniqueness, NOT the
four-step path *existence/counting* or the sparse power saving.
-/

namespace OpenAI086

/-- An alternating path is recorded as consecutive pairs of vertices
`(v,w)` starting from a left-side vertex `u`. -/
def alternatingPathValid {U V C : Type*}
    (G : BipartiteProperColoring U V C) : U → List (V × U) → Prop
  | _, [] => True
  | u, (v, w) :: tail =>
      G.adjacent u v ∧ G.adjacent w v ∧ alternatingPathValid G w tail

/-- Color sequence of consecutive left-to-right and right-to-left
edges. The next pair is read from the previous pair's endpoint. -/
def alternatingPathColors {U V C : Type*}
    (G : BipartiteProperColoring U V C) : U → List (V × U) → List (C × C)
  | _, [] => []
  | u, (v, w) :: tail =>
      (G.color u v, G.color w v) :: alternatingPathColors G w tail

/-- For a proper edge coloring, two valid alternating paths with the
same start and the same ordered colors have exactly the same vertices,
at any finite even length. No acyclicity or vertex distinctness is needed. -/
theorem alternating_paths_determined_by_colors
    {U V C : Type*} (G : BipartiteProperColoring U V C)
    (start : U) (p q : List (V × U))
    (hp : alternatingPathValid G start p)
    (hq : alternatingPathValid G start q)
    (hcolors : alternatingPathColors G start p =
      alternatingPathColors G start q) : p = q := by
  induction p generalizing start q with
  | nil =>
      cases q with
      | nil => rfl
      | cons step tail =>
          simp [alternatingPathColors] at hcolors
  | cons step ps ih =>
      cases q with
      | nil =>
          simp [alternatingPathColors] at hcolors
      | cons step' qs =>
          rcases step with ⟨v, w⟩
          rcases step' with ⟨v', w'⟩
          change G.adjacent start v ∧ G.adjacent w v ∧
            alternatingPathValid G w ps at hp
          change G.adjacent start v' ∧ G.adjacent w' v' ∧
            alternatingPathValid G w' qs at hq
          rcases hp with ⟨hp₁, hp₂, hpRest⟩
          rcases hq with ⟨hq₁, hq₂, hqRest⟩
          have hcons :
              (G.color start v, G.color w v) :: alternatingPathColors G w ps =
              (G.color start v', G.color w' v') :: alternatingPathColors G w' qs :=
            hcolors
          obtain ⟨hhead, htail⟩ := List.cons.inj hcons
          have hv : v = v' :=
            G.left_unique start v v' hp₁ hq₁ (congrArg Prod.fst hhead)
          subst v'
          have hw : w = w' :=
            G.right_unique v w w' hp₂ hq₂ (congrArg Prod.snd hhead)
          subst w'
          have hrest : ps = qs := ih w qs hpRest hqRest htail
          simp [hrest]

end OpenAI086
