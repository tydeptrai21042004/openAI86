import OpenAI086.PaperV52ParameterOrder

/-! Section 10.3, p.92: actual integer ceiling and polynomial depth cost.
These are numerical consequences, not the preceding analytic complexity bounds. -/
namespace OpenAI086

/-- On (0,1], increasing the exponent decreases the power. -/
theorem v53_small_base_power (x a b : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hab : a ≤ b) : x^b ≤ x^a := by
  simp only [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  exact mul_le_mul_of_nonpos_right hab hl

/-- The exact ceiling P from the paper lies between eta^(-alpha) and
2 eta^(-alpha). No ceiling-power hypothesis is needed. -/
theorem v53_ceiling_bounds (η α : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hα : 0 ≤ α) :
    η^(-α) ≤ (Int.ceil (η^(-α)) : ℝ) ∧
    (Int.ceil (η^(-α)) : ℝ) ≤ 2*η^(-α) := by
  have hx : 1 ≤ η^(-α) := by
    simpa using v53_small_base_power η (-α) 0 hη hη1 (neg_nonpos.mpr hα)
  have hlo := Int.le_ceil (η^(-α))
  have hhi := Int.ceil_lt_add_one (η^(-α))
  exact ⟨hlo, by linarith⟩

theorem v53_ceiling_power (η α C : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hα : 0 ≤ α) (hC : 0 ≤ C) :
    (Int.ceil (η^(-α)) : ℝ)^C ≤ 2^C * η^(-α*C) := by
  obtain ⟨hlo,hhi⟩ := v53_ceiling_bounds η α hη hη1 hα
  have hP : 0 ≤ (Int.ceil (η^(-α)) : ℝ) :=
    (Real.rpow_nonneg hη.le _).trans hlo
  calc
    _ ≤ (2*η^(-α))^C := Real.rpow_le_rpow hP hhi hC
    _ = 2^C * η^(-α*C) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hη.le _),
        ← Real.rpow_mul hη.le]

theorem v53_main_power (η α ε C : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hα : 0 ≤ α) (hε : 0 < ε) (hC : 0 ≤ C) (hgap : α*C < ε/2) :
    η^ε * (Int.ceil (η^(-α)) : ℝ)^C ≤ 2^C * η^(ε/2) :=
  v52_quality_power_from_ceiling_power η α ε C _ hη hη1 hε hC hgap
    (v53_ceiling_power η α C hη hη1.le hα hC)

/-- Unlike the V52 special case, K+2 may grow like P^C5. -/
theorem v53_polynomial_side_cost (P K G C0 C5 β : ℝ)
    (hP : 1 ≤ P) (hK0 : 0 ≤ K+2) (hC0 : 0 < C0)
    (hK : K+2 ≤ C0*P^C5) (hG : G ≤ P^(1/8:ℝ))
    (hβ : 0 ≤ β) (hgap : C5*β ≤ 1/8) :
    P^(-1/2:ℝ)*G*(K+2)^β ≤ C0^β*P^(-1/4:ℝ) := by
  have hPpos : 0 < P := by linarith
  have hKpow : (K+2)^β ≤ C0^β*P^(1/8:ℝ) := by
    calc
      _ ≤ (C0*P^C5)^β := Real.rpow_le_rpow hK0 hK hβ
      _ = C0^β*P^(C5*β) := by
        rw [Real.mul_rpow hC0.le (Real.rpow_nonneg hPpos.le _), ← Real.rpow_mul hPpos.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP hgap) (Real.rpow_nonneg hC0.le _)
  have hp : G*(K+2)^β ≤ P^(1/8:ℝ)*(C0^β*P^(1/8:ℝ)) :=
    mul_le_mul hG hKpow (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hPpos.le _)
  calc
    _ = P^(-1/2:ℝ)*(G*(K+2)^β) := by ring
    _ ≤ P^(-1/2:ℝ)*(P^(1/8:ℝ)*(C0^β*P^(1/8:ℝ))) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hPpos.le _)
    _ = C0^β*((P^(-1/2:ℝ)*P^(1/8:ℝ))*P^(1/8:ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
      congr 1
      norm_num

/-- Second estimate after the choice P=ceil(eta^(-alpha)). -/
theorem v53_ceiling_inverse_quarter (η α : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hα : 0 ≤ α) :
    (Int.ceil (η^(-α)) : ℝ)^(-1/4:ℝ) ≤ η^(α/4) := by
  obtain ⟨hlo,_⟩ := v53_ceiling_bounds η α hη hη1 hα
  have hx : 0 < η^(-α) := Real.rpow_pos_of_pos hη _
  have hp : 0 < (Int.ceil (η^(-α)) : ℝ) := hx.trans_le hlo
  have hlog : Real.log (η^(-α)) ≤ Real.log (Int.ceil (η^(-α)) : ℝ) :=
    Real.log_le_log hx hlo
  calc
    _ ≤ (η^(-α))^(-1/4:ℝ) := by
      rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hx]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlog (by norm_num))
    _ = _ := by
      rw [← Real.rpow_mul hη.le]
      congr 1
      ring

end OpenAI086
