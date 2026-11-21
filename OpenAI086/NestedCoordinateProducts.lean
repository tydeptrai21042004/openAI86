import Mathlib
import OpenAI086.CoordinateProjections

/-!
# A depth-uniform square-energy estimate for many COMMUTING layers

The manuscript's Lemma 3.3 concerns ordered products of generally
NONCOMMUTING orthogonal projections. The coordinate projections here
commute. Their product is exactly a projection onto the intersection of
all selected coordinates. Hence a full square-energy estimate is available
with constant one, for *any* number of layers and depth generations.

This is a rigorous, nontrivial restricted case of the intended mechanism,
not the noncommutative Rademacher--Menshov estimate from the manuscript.
-/

namespace OpenAI086

/-- Two coordinate projections compose to the projection onto the
intersection of their coordinate sets. -/
theorem coordMask_intersection {n : ℕ} (S T : Finset (Fin n))
    (x : Fin n → ℝ) :
    coordMask S (coordMask T x) = coordMask (S ∩ T) x := by
  funext i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
    simp [coordMask, hiS, hiT]

/-- Recursive intersection of a finite list of coordinate sets. -/
def commonMaskList {n : ℕ} : List (Finset (Fin n)) → Finset (Fin n)
  | [] => Finset.univ
  | S :: rest => S ∩ commonMaskList rest

/-- Composition in the stated order, with the rightmost layer applied
first. The order turns out not to matter for coordinate projections. -/
def applyCoordLayers {n : ℕ} (layers : List (Finset (Fin n)))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  layers.foldr (fun S acc => coordMask S acc) x

/-- An arbitrary finite number of commuting coordinate projections
collapses to one intersection projection. -/
theorem applyCoordLayers_eq_common {n : ℕ}
    (layers : List (Finset (Fin n))) (x : Fin n → ℝ) :
    applyCoordLayers layers x = coordMask (commonMaskList layers) x := by
  induction layers with
  | nil =>
      simp [applyCoordLayers, commonMaskList, coordMask]
  | cons S rest ih =>
      change coordMask S (applyCoordLayers rest x) =
        coordMask (S ∩ commonMaskList rest) x
      rw [ih, coordMask_intersection]

/-- Common coordinate set across `m` independent projection layers. -/
def commonMask {m n : ℕ} (S : Fin m → Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ j : Fin m, i ∈ S j)

/-- Increasing each layer increases the common-coordinate projection. -/
theorem commonMask_mono {m n : ℕ}
    (S T : Fin m → Finset (Fin n))
    (h : ∀ j : Fin m, S j ⊆ T j) :
    commonMask S ⊆ commonMask T := by
  intro i hi
  simp only [commonMask, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  intro j
  exact h j (hi j)

/-- A family of commuting projection products at any depth. -/
def coordMultiProduct {m n : ℕ}
    (S : Fin m → ℕ → Finset (Fin n)) (k : ℕ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  coordMask (commonMask (fun j => S j k)) x

/-- The square-function energy for arbitrarily many coordinate-projection
families has a constant **one**, independent of the number of layers `m`
and the number of scale generations `N`. Noncommuting families remain open. -/
theorem coordMultiProduct_depth_uniform_energy {m n : ℕ}
    (S : Fin m → ℕ → Finset (Fin n)) (x : Fin n → ℝ)
    (hS : ∀ (j : Fin m) (k : ℕ), S j k ⊆ S j (k + 1))
    (N : ℕ) :
    (∑ k ∈ Finset.range N,
      coordEnergy (fun i =>
        coordMultiProduct S (k + 1) x i - coordMultiProduct S k x i))
      ≤ coordEnergy x := by
  have hnested (k : ℕ) :
      commonMask (fun j => S j k) ⊆
        commonMask (fun j => S j (k + 1)) := by
    apply commonMask_mono
    intro j
    exact hS j k
  simpa only [coordMultiProduct] using
    (coordMask_chain_energy
      (fun k => commonMask (fun j => S j k)) x hnested N)

end OpenAI086
