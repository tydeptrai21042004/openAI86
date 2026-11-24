import Mathlib

/-! Lemma 4.11 (p.27), second assertion: integrate the product majorant in
pair coordinates. This is an actual iterated Lebesgue integral bound.
The progression-coordinate Jacobian and U³ first assertion remain open. -/
namespace OpenAI086
open MeasureTheory

/-- The two L1 inputs give a factorized bound once in the two independent
progression coordinates. All integrability conditions are explicit. -/
theorem v26_pair_coordinate_L1 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (F : X → Y → ℂ) (a : X → ℝ) (b : Y → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ha : Integrable a μ) (hb : Integrable b ν)
    (han : ∀ x, 0 ≤ a x) (hbn : ∀ y, 0 ≤ b y)
    (hF : ∀ x, Integrable (F x) ν)
    (houter : Integrable (fun x => ∫ y, F x y ∂ν) μ)
    (hbound : ∀ x y, ‖F x y‖ ≤ C*a x*b y) :
    ‖∫ x, (∫ y, F x y ∂ν) ∂μ‖ ≤ C*(∫ x, a x ∂μ)*(∫ y, b y ∂ν) := by
  have hinner (x : X) : ‖∫ y, F x y ∂ν‖ ≤ C*a x*(∫ y, b y ∂ν) := by
    calc
      _ ≤ ∫ y, ‖F x y‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (C*a x)*b y ∂ν := integral_mono (hF x).norm
        (hb.const_mul _) (hbound x)
      _ = _ := by rw [integral_const_mul]
  have hB : Integrable (fun x => C*a x*(∫ y, b y ∂ν)) μ :=
    (ha.const_mul C).mul_const _
  calc
    _ ≤ ∫ x, ‖∫ y, F x y ∂ν‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*a x*(∫ y, b y ∂ν) ∂μ := integral_mono houter.norm hB hinner
    _ = _ := by rw [integral_mul_const, integral_const_mul]

end OpenAI086
