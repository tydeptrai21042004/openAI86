import SourceV60CoreSummation

/-! V61, Proposition 9.3 final cell summation. The numerical errors are
summed with exponent one, after clipping the full cell contribution.
The analytic path-power budget must still be supplied by the earlier
core counting and frequency/amplitude arguments. -/
namespace OpenAI086.SourceV61
open scoped BigOperators

/-- Finite weighted version of the final minimum argument, allowing a
different finite principal-term index set at each cell. -/
theorem weighted_core_min {I J : Type*} (cells : Finset I) (terms : I → Finset J)
    (w a err : I → ℝ) (x : I → J → ℝ) (η p B E : ℝ)
    (hη : 0 ≤ η) (hp : 0 < p) (hp1 : p ≤ 1)
    (hw : ∀ i ∈ cells, 0 ≤ w i) (he : ∀ i ∈ cells, 0 ≤ err i)
    (hx : ∀ i ∈ cells, ∀ j ∈ terms i, 0 ≤ x i j)
    (ha : ∀ i ∈ cells, a i ≤ (∑ j ∈ terms i, x i j) + err i)
    (hB : (∑ i ∈ cells, w i * ∑ j ∈ terms i, (x i j)^p) ≤ B)
    (hE : (∑ i ∈ cells, w i * err i) ≤ E) :
    (∑ i ∈ cells, w i * min η (a i)) ≤ η^(1-p)*B + E := by
  calc
    _ ≤ ∑ i ∈ cells, w i * (η^(1-p) * (∑ j ∈ terms i, (x i j)^p) + err i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (OpenAI086.SourceV60.paper_min_with_error (terms i) (x i) hη hp hp1
          (hx i hi) (he i hi) (ha i hi)) (hw i hi)
    _ = η^(1-p)*(∑ i ∈ cells, w i * ∑ j ∈ terms i, (x i j)^p) +
        (∑ i ∈ cells, w i * err i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hη _)) hE

end OpenAI086.SourceV61
#print axioms OpenAI086.SourceV61.weighted_core_min
