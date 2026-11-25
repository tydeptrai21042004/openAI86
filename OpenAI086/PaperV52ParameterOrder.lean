import Mathlib

/-!
V52 formalization of the explicit parameter-order arithmetic on p.92.
The analytic estimates that provide the complexity bounds are not proved
here.  This module proves the numerical choices and the side-cost power
reduction once those bounds are available.
-/
namespace OpenAI086

/-- Choose q close enough to 2 and alpha small enough for the powered
main term.  The numerical thresholds are exactly those used in Section
10.3: C19*C5*(q-2) < 1/8 and alpha*C4 < epsilon/2. -/
theorem v52_choose_parameter_order
    (C19 C5 C4 ε : ℝ)
    (h19 : 0 < C19) (h5 : 0 < C5)
    (h4 : 0 ≤ C4) (hε : 0 < ε) :
    ∃ q α : ℝ,
      2 < q ∧ q < 3 ∧ 0 < α ∧
      C19*C5*(q-2) < 1/8 ∧ α*C4 < ε/2 := by
  let d : ℝ := 1/(16*(C19*C5+1))
  let α : ℝ := ε/(4*(C4+1))
  have hprod : 0 < C19*C5 := mul_pos h19 h5
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdsmall : d < 1/16 := by
    dsimp [d]
    apply (div_lt_iff₀ (by positivity : 0 < 16*(C19*C5+1))).2
    nlinarith
  have halphapos : 0 < α := by dsimp [α]; positivity
  have halphasmall : α*C4 < ε/4 := by
    dsimp [α]
    apply (div_lt_iff₀ (by positivity : 0 < 4*(C4+1))).2
    nlinarith [hε]
  refine ⟨2+d, α, ?_, ?_, halphapos, ?_, ?_⟩
  · linarith
  · linarith
  · have hbound : C19*C5*d < 1/16 := by
      dsimp [d]
      apply (div_lt_iff₀ (by positivity : 0 < 16*(C19*C5+1))).2
      nlinarith
    dsimp
    nlinarith
  · linarith

/-- The side-cost reduction in Section 10.3. If the strong overhead is
at most P^(1/8), the block length is at most P, and the q-exponent is
below 1/8, then the complete side factor is at most P^(-1/4). -/
theorem v52_side_cost_power
    (P K G0 β : ℝ)
    (hP : 1 ≤ P) (hK0 : 0 ≤ K+2) (hK : K+2 ≤ P)
    (hG0 : G0 ≤ P^(1/8 : ℝ))
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1/8) :
    P^(-1/2 : ℝ)*G0*(K+2)^β ≤ P^(-1/4 : ℝ) := by
  have hPpos : 0 < P := by linarith
  have hKpow : (K+2)^β ≤ P^β := Real.rpow_le_rpow hK0 hK hβ0
  have hPpow : P^β ≤ P^(1/8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP hβ
  have hsmall : (K+2)^β ≤ P^(1/8 : ℝ) := hKpow.trans hPpow
  have hprod : G0*(K+2)^β ≤ P^(1/8 : ℝ)*P^(1/8 : ℝ) :=
    mul_le_mul hG0 hsmall (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hPpos.le _)
  have hpowid : P^(1/8 : ℝ)*P^(1/8 : ℝ) = P^(1/4 : ℝ) := by
    rw [← Real.rpow_add hPpos]
    congr 1
    norm_num
  calc
    _ = P^(-1/2 : ℝ)*(G0*(K+2)^β) := by ring
    _ ≤ P^(-1/2 : ℝ)*(P^(1/8 : ℝ)*P^(1/8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hPpos.le _)
    _ = P^(-1/2 : ℝ)*P^(1/4 : ℝ) := by rw [hpowid]
    _ = P^(-1/4 : ℝ) := by
      rw [← Real.rpow_add hPpos]
      congr 1
      norm_num

/-- The powered main-term reduction in Section 10.3.  The separate
`hPpower` premise is the ceiling estimate for P; this theorem performs the
remaining exponent comparison without hiding the strict eta<1 requirement. -/
theorem v52_quality_power_from_ceiling_power
    (η α ε C4 P : ℝ)
    (hη : 0 < η) (hη1 : η < 1)
    (hε : 0 < ε) (hC4 : 0 ≤ C4)
    (hgap : α*C4 < ε/2)
    (hPpower : P^C4 ≤ 2^C4 * Real.rpow η (-α*C4)) :
    Real.rpow η ε * P^C4 ≤ 2^C4 * Real.rpow η (ε/2) := by
  have hηpow : 0 ≤ Real.rpow η ε := Real.rpow_nonneg hη.le _
  have hexp : ε/2 ≤ ε-α*C4 := by linarith
  have hcompare : Real.rpow η (ε-α*C4) ≤ Real.rpow η (ε/2) := by
    rw [Real.rpow_def_of_pos hη, Real.rpow_def_of_pos hη]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right hexp (Real.log_neg hη hη1).le
  calc
    _ ≤ Real.rpow η ε * (2^C4 * Real.rpow η (-α*C4)) :=
      mul_le_mul_of_nonneg_left hPpower hηpow
    _ = 2^C4 * (Real.rpow η ε * Real.rpow η (-α*C4)) := by ring
    _ = 2^C4 * Real.rpow η (ε-α*C4) := by
      congr 1
      rw [← Real.rpow_add hη]
      congr 1
      ring
    _ ≤ 2^C4 * Real.rpow η (ε/2) :=
      mul_le_mul_of_nonneg_left hcompare (Real.rpow_nonneg (by norm_num : 0 ≤ (2:ℝ)) _)


end OpenAI086
