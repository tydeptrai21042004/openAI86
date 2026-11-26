import SourceV61WeightedCore

/-! Proposition 9.3: derive the global weighted power budget from a
uniform path budget and a finite leaf partition. The leaves represent
measurable disjoint atoms of the retained tree; their weights are lengths.
No analytic estimate for a path or numerical-error budget is asserted here. -/
namespace OpenAI086.SourceV62
open scoped BigOperators

/-- Exact finite Tonelli identity: a cell weight is the sum of the weights
of leaves descending from it. -/
theorem leaf_weighted_sum {I L : Type*} (cells : Finset I) (leaves : Finset L)
    (w : L → ℝ) (onPath : I → L → Prop) [DecidableRel onPath] (a : I → ℝ) :
    (∑ i ∈ cells, (∑ l ∈ leaves, if onPath i l then w l else 0) * a i) =
      ∑ l ∈ leaves, w l * (∑ i ∈ cells, if onPath i l then a i else 0) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : onPath i l <;> simp [h, mul_comm]

/-- A bound holding on each leaf implies a length-weighted bound, with
no dependence on the number of cells or the number of leaves. -/
theorem leaf_budget {I L : Type*} (cells : Finset I) (leaves : Finset L)
    (w : L → ℝ) (onPath : I → L → Prop) [DecidableRel onPath] (a : I → ℝ)
    (B : ℝ) (hw : ∀ l ∈ leaves, 0 ≤ w l)
    (hpath : ∀ l ∈ leaves, (∑ i ∈ cells, if onPath i l then a i else 0) ≤ B) :
    (∑ i ∈ cells, (∑ l ∈ leaves, if onPath i l then w l else 0) * a i) ≤
      B * ∑ l ∈ leaves, w l := by
  rw [leaf_weighted_sum cells leaves w onPath a]
  calc
    _ ≤ ∑ l ∈ leaves, w l * B :=
      Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (hpath l hl) (hw l hl)
    _ = _ := by rw [Finset.sum_mul, mul_comm]

/-- Apply the original cell clipping only after transferring the path
power budget to cell weights; sum numerical errors at power one. -/
theorem core_from_leaf_budgets {I L J : Type*} (cells : Finset I) (leaves : Finset L)
    (terms : I → Finset J) (w : L → ℝ) (onPath : I → L → Prop) [DecidableRel onPath]
    (a err : I → ℝ) (x : I → J → ℝ) (η p B E : ℝ)
    (hη : 0 ≤ η) (hp : 0 < p) (hp1 : p ≤ 1)
    (hw : ∀ l ∈ leaves, 0 ≤ w l) (he : ∀ i ∈ cells, 0 ≤ err i)
    (hx : ∀ i ∈ cells, ∀ j ∈ terms i, 0 ≤ x i j)
    (ha : ∀ i ∈ cells, a i ≤ (∑ j ∈ terms i, x i j) + err i)
    (hB : ∀ l ∈ leaves, (∑ i ∈ cells, if onPath i l then
      (∑ j ∈ terms i, (x i j)^p) else 0) ≤ B)
    (hE : ∀ l ∈ leaves, (∑ i ∈ cells, if onPath i l then err i else 0) ≤ E) :
    (∑ i ∈ cells, (∑ l ∈ leaves, if onPath i l then w l else 0) * min η (a i)) ≤
      (η^(1-p)*B + E) * ∑ l ∈ leaves, w l := by
  have hweights : ∀ i ∈ cells, 0 ≤ ∑ l ∈ leaves, if onPath i l then w l else 0 := by
    intro i hi
    apply Finset.sum_nonneg
    intro l hl
    by_cases h : onPath i l <;> simp [h, hw l hl]
  have h := OpenAI086.SourceV61.weighted_core_min cells terms
    (fun i => ∑ l ∈ leaves, if onPath i l then w l else 0) a err x η p
    (B * ∑ l ∈ leaves, w l) (E * ∑ l ∈ leaves, w l)
    hη hp hp1 hweights he hx ha
    (leaf_budget cells leaves w onPath (fun i => ∑ j ∈ terms i, (x i j)^p) B hw hB)
    (leaf_budget cells leaves w onPath err E hw hE)
  refine h.trans (le_of_eq ?_)
  ring

end OpenAI086.SourceV62
#print axioms OpenAI086.SourceV62.leaf_weighted_sum
#print axioms OpenAI086.SourceV62.leaf_budget
#print axioms OpenAI086.SourceV62.core_from_leaf_budgets
