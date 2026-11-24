import OpenAI086.PaperSparseNeighborhood
import OpenAI086.ColoredPathUniqueness

/-! Lemma 9.1, p.83: actual endpoint-constrained walk enumeration and
injective encoding of those walks by four colors. This connects the
numeric codegree-product count to the proper-coloring argument. -/
namespace OpenAI086

noncomputable def v40Walks {U V C : Type*} [Fintype U] [Fintype V]
    (G : BipartiteProperColoring U V C) (u w : U) : Finset (U × V × V) := by
  classical
  exact Finset.univ.filter (fun p => G.adjacent u p.2.1 ∧ G.adjacent p.1 p.2.1 ∧
    G.adjacent p.1 p.2.2 ∧ G.adjacent w p.2.2)

def v40WalkColors {U V C : Type*} (G : BipartiteProperColoring U V C)
    (u w : U) (p : U × V × V) : C × C × C × C :=
  (G.color u p.2.1, G.color p.1 p.2.1, G.color p.1 p.2.2, G.color w p.2.2)

/-- Injectivity on actual valid endpoint paths, allowing repeated vertices. -/
theorem v40_walk_color_injective {U V C : Type*} [Fintype U] [Fintype V]
    (G : BipartiteProperColoring U V C) (u w : U) :
    Set.InjOn (v40WalkColors G u w) (↑(v40Walks G u w) : Set (U × V × V)) := by
  classical
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.mp (show a ∈ v40Walks G u w from ha)).2
  have hb' := (Finset.mem_filter.mp (show b ∈ v40Walks G u w from hb)).2
  obtain ⟨h1,h2,h3,h4⟩ := ha'
  obtain ⟨k1,k2,k3,k4⟩ := hb'
  obtain ⟨hv,hz,ht,_⟩ := four_edge_colors_determine_path G u a.1 w b.1 w
    a.2.1 a.2.2 b.2.1 b.2.2 h1 h2 h3 h4 k1 k2 k3 k4
    (congrArg Prod.fst hab) (congrArg (fun x => x.2.1) hab)
    (congrArg (fun x => x.2.2.1) hab) (congrArg (fun x => x.2.2.2) hab)
  exact Prod.ext hz (Prod.ext hv ht)

/-- The cardinal of the actual color image equals that of the paths. -/
theorem v40_color_count {U V C : Type*} [Fintype U] [Fintype V] [DecidableEq C]
    (G : BipartiteProperColoring U V C) (u w : U) :
    ((v40Walks G u w).image (v40WalkColors G u w)).card = (v40Walks G u w).card := by
  exact Finset.card_image_iff.mpr (v40_walk_color_injective G u w)

/-- The adjacency matrix determined by the original graph predicate. -/
noncomputable def v40GraphMatrix {U V C : Type*} (G : BipartiteProperColoring U V C)
    (u : U) (v : V) : ℝ := by classical exact if G.adjacent u v then 1 else 0

/-- The count of actual four-step walks with fixed endpoints is the
sum of products of the two codegrees. This is not the closed C4 count. -/
theorem v40_walk_count_identity {U V C : Type*} [Fintype U] [Fintype V]
    (G : BipartiteProperColoring U V C) (u w : U) :
    ((v40Walks G u w).card : ℝ) =
      ∑ z : U, finiteCodegree (v40GraphMatrix G) u z * finiteCodegree (v40GraphMatrix G) z w := by
  classical
  calc
    _ = ∑ _p ∈ v40Walks G u w, (1:ℝ) := by simp
    _ = ∑ p : U × V × V, if G.adjacent u p.2.1 ∧ G.adjacent p.1 p.2.1 ∧
          G.adjacent p.1 p.2.2 ∧ G.adjacent w p.2.2 then (1:ℝ) else 0 := by
          unfold v40Walks
          rw [Finset.sum_filter]
    _ = ∑ z : U, ∑ v : V, ∑ t : V, (v40GraphMatrix G u v * v40GraphMatrix G z v) *
          (v40GraphMatrix G z t * v40GraphMatrix G w t) := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro z _
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro t _
          unfold v40GraphMatrix
          by_cases h1 : G.adjacent u v <;> by_cases h2 : G.adjacent z v <;>
            by_cases h3 : G.adjacent z t <;> by_cases h4 : G.adjacent w t <;>
            simp [h1,h2,h3,h4]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro z _
          unfold finiteCodegree
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]

/-- Apply the dense graph selection to a proper coloring. Returns the
actual image cardinality of ordered four-color sequences. -/
theorem v40_dense_colored_paths {U V C : Type*} [Fintype U] [Fintype V] [DecidableEq C]
    (G : BipartiteProperColoring U V C) (M η : ℝ) (hM : 0 < M) (hη : 0 < η)
    (hU : (Fintype.card U : ℝ) ≤ M) (hV : (Fintype.card V : ℝ) ≤ 2*M)
    (hedge : η*M^2 ≤ ∑ v, v40Degree (v40GraphMatrix G) v) :
    ∃ B : Finset U, η*M/5 ≤ (B.card : ℝ) ∧
      ∀ u ∈ B, ∀ w ∈ B, η^5*M^3/(8*1600^2) ≤
        (((v40Walks G u w).image (v40WalkColors G u w)).card : ℝ) := by
  classical
  let edge : U → V → Bool := fun u v => decide (G.adjacent u v)
  have hmat : v40Adj edge = v40GraphMatrix G := by
    funext u v
    simp [edge, v40Adj, v40GraphMatrix]
  obtain ⟨B,hB,hwalk⟩ := v40_dense_graph_walks edge M η hM hη hU hV
    (by rwa [hmat])
  refine ⟨B,hB,?_⟩
  intro u hu w hw
  rw [v40_color_count, v40_walk_count_identity]
  simpa only [hmat] using hwalk u hu w hw

end OpenAI086
