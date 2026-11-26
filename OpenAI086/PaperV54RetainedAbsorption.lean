import OpenAI086.PaperV53ParameterCompletion

/-! Section 10.3: combine the actual ceiling, polynomial depth budget,
and numerical error into a single power of η. The retained-cell analytic
bound and the large-starting-log complexity inequalities remain inputs. -/
namespace OpenAI086

theorem v54_retained_quality_power
    (η α ε C C0 C5 β K G CN R cost err A B E : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hα : 0 < α) (hε : 0 < ε)
    (hC : 0 ≤ C) (hgap : α*C < ε/2)
    (hC0 : 0 < C0) (hK0 : 0 ≤ K+2) (hβ : 0 ≤ β) (hsidegap : C5*β ≤ 1/8)
    (hK : K+2 ≤ C0*(Int.ceil (η^(-α)) : ℝ)^C5)
    (hG : G ≤ (Int.ceil (η^(-α)) : ℝ)^(1/8:ℝ))
    (hCN : 0 ≤ CN) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (herr : err ≤ E*η^(min (ε/2) (α/4))*R)
    (hcost : cost ≤ (A*η^ε*(Int.ceil (η^(-α)) : ℝ)^C +
      B*(1+CN)*(Int.ceil (η^(-α)) : ℝ)^(-1/2:ℝ)*G*(K+2)^β)*R+err) :
    cost ≤ (A*2^C + B*C0^β + E)*η^(min (ε/2) (α/4))*(1+CN)*R := by
  let P : ℝ := (Int.ceil (η^(-α)) : ℝ)
  let c : ℝ := min (ε/2) (α/4)
  have hx : 1 ≤ η^(-α) := by
    simpa using v53_small_base_power η (-α) 0 hη hη1.le (neg_nonpos.mpr hα.le)
  have hP : 1 ≤ P := hx.trans (v53_ceiling_bounds η α hη hη1.le hα.le).1
  have hm : η^ε*P^C ≤ 2^C*η^c :=
    (v53_main_power η α ε C hη hη1 hα.le hε hC hgap).trans
      (mul_le_mul_of_nonneg_left
        (v53_small_base_power η c (ε/2) hη hη1.le (min_le_left _ _)) (by positivity))
  have hs : P^(-1/2:ℝ)*G*(K+2)^β ≤ C0^β*η^c := by
    calc
      _ ≤ C0^β*P^(-1/4:ℝ) := v53_polynomial_side_cost P K G C0 C5 β hP hK0 hC0 hK hG hβ hsidegap
      _ ≤ C0^β*η^(α/4) := mul_le_mul_of_nonneg_left
        (v53_ceiling_inverse_quarter η α hη hη1.le hα.le) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (v53_small_base_power η c (α/4) hη hη1.le (min_le_right _ _)) (by positivity)
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hA) hR
  have hside := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (mul_nonneg hB (by linarith : 0 ≤ 1+CN))) hR
  have haux : 0 ≤ (A*2^C+E)*η^c*CN*R := by positivity
  change err ≤ E*η^c*R at herr
  change cost ≤ (A*η^ε*P^C + B*(1+CN)*P^(-1/2:ℝ)*G*(K+2)^β)*R+err at hcost
  change cost ≤ (A*2^C+B*C0^β+E)*η^c*(1+CN)*R
  calc
    cost ≤ (A*η^ε*P^C + B*(1+CN)*P^(-1/2:ℝ)*G*(K+2)^β)*R+err := hcost
    _ = (A*(η^ε*P^C))*R + (B*(1+CN)*(P^(-1/2:ℝ)*G*(K+2)^β))*R+err := by ring
    _ ≤ (A*(2^C*η^c))*R + (B*(1+CN)*(C0^β*η^c))*R + E*η^c*R := by linarith
    _ ≤ _ := by
      calc
        _ ≤ (A*(2^C*η^c))*R + (B*(1+CN)*(C0^β*η^c))*R + E*η^c*R +
            (A*2^C+E)*η^c*CN*R := le_add_of_nonneg_right haux
        _ = _ := by ring

end OpenAI086
