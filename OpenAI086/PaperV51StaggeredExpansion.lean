import Mathlib

/-!
V51 exact algebraic expansion used by the staggered-accuracy arguments
in Section 5.  This is the product identity only; the paper's estimates
for the increment factors, predictor moments, and delayed projections
remain separate analytic obligations.
-/
namespace OpenAI086

/-- Four-slot telescoping with the earlier factors taken at the new
accuracy and the later factors at the old accuracy. -/
theorem v51_four_slot_product_telescoping
    {R : Type*} [CommRing R]
    (a0 a1 a2 a3 b0 b1 b2 b3 : R) :
    a0*a1*a2*a3 - b0*b1*b2*b3 =
      (a0-b0)*a1*a2*a3 +
      b0*(a1-b1)*a2*a3 +
      b0*b1*(a2-b2)*a3 +
      b0*b1*b2*(a3-b3) := by
  ring

/-- A four-slot product difference is controlled by the four one-slot
increments; no hidden count of the intermediate accuracy levels occurs. -/
theorem v51_four_slot_product_difference_bound
    (a0 a1 a2 a3 b0 b1 b2 b3 : ℂ) :
    ‖a0*a1*a2*a3-b0*b1*b2*b3‖ ≤
      ‖a0-b0‖*‖a1‖*‖a2‖*‖a3‖ +
      ‖b0‖*‖a1-b1‖*‖a2‖*‖a3‖ +
      ‖b0‖*‖b1‖*‖a2-b2‖*‖a3‖ +
      ‖b0‖*‖b1‖*‖b2‖*‖a3-b3‖ := by
  rw [v51_four_slot_product_telescoping]
  calc
    _ ≤ ‖(a0-b0)*a1*a2*a3‖ +
        ‖b0*(a1-b1)*a2*a3‖ +
        ‖b0*b1*(a2-b2)*a3‖ +
        ‖b0*b1*b2*(a3-b3)‖ := by
      calc
        _ = ‖((a0-b0)*a1*a2*a3 + b0*(a1-b1)*a2*a3) +
            (b0*b1*(a2-b2)*a3 + b0*b1*b2*(a3-b3))‖ := by congr 1 <;> ring
        _ ≤ ‖(a0-b0)*a1*a2*a3 + b0*(a1-b1)*a2*a3‖ +
            ‖b0*b1*(a2-b2)*a3 + b0*b1*b2*(a3-b3)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ = _ := by simp [norm_mul, mul_assoc, add_assoc]

end OpenAI086
