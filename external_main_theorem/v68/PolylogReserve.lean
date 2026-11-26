import TrilinearHT.Auto.Sec16_3SummingUpdateLevels

/-! Section 10.3: the printed overhead permits any fixed logarithmic
power, not just a square. Derive the P^(1/8) reserve when P is the actual
ceiling of the inverse quality power. No bound for the analytic overhead
is postulated as a theorem: it remains a premise for the application. -/
namespace OpenAI086.ReferenceV68
open Auto Filter Asymptotics

/-- Every fixed polynomial in log(2x) is negligible compared with a
positive stretched power of x. -/
theorem eventually_log_power_le {C β θ : ℝ} (d : ℕ)
    (hC : 0 ≤ C) (hβ : 0 < β) (hθ : 0 < θ) :
    ∀ᶠ x : ℝ in atTop, C * (1 + Real.log (2*x)) ^ d ≤ β * x ^ θ := by
  have hl : (fun x : ℝ => Real.log x ^ (d : ℝ)) =o[atTop] fun x => x ^ θ :=
    isLittleO_log_rpow_rpow_atTop (d : ℝ) hθ
  have hsmall := (hl.const_mul_left (C * (2 : ℝ)^d)).def hβ
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp (1 + Real.log 2))] with x hx hxlarge
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hxlarge
  have hxlog : 1 + Real.log 2 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxlarge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hxlog0 : 0 ≤ Real.log x := by linarith
  have heq : Real.log (2*x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hxpos.ne'
  have hpow : (1 + Real.log (2*x))^d ≤ (2 * Real.log x)^d := by
    apply pow_le_pow_left₀
    · rw [heq]; linarith
    · rw [heq]; linarith
  have hnorm1 : 0 ≤ C * (2 : ℝ)^d * (Real.log x)^d := by positivity
  have hnorm2 : 0 ≤ x ^ θ := Real.rpow_nonneg hxpos.le _
  simp only [Real.rpow_natCast] at hx
  rw [Real.norm_of_nonneg hnorm1, Real.norm_of_nonneg hnorm2] at hx
  calc
    _ ≤ C * (2 * Real.log x)^d := mul_le_mul_of_nonneg_left hpow hC
    _ = C * (2 : ℝ)^d * (Real.log x)^d := by rw [mul_pow]; ring
    _ ≤ _ := hx

/-- Paper reserve for the actual integer choice P=ceil(η^(-α)) with
η=exp(-k^θ). Every fixed logarithmic power is allowed. -/
theorem eventually_ceiling_overhead {C α θ : ℝ} (d : ℕ)
    (hC : 0 ≤ C) (hα : 0 < α) (hθ : 0 < θ) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (C * (1 + Real.log (2 * (k : ℝ))) ^ d) ≤
        (Int.ceil ((Real.exp (-((k : ℝ)^θ))) ^ (-α)) : ℝ) ^ (1/8 : ℝ) := by
  have hs := tendsto_natCast_atTop_atTop.eventually
    (eventually_log_power_le (C := C) (β := α/8) (θ := θ) d hC (by positivity) hθ)
  filter_upwards [hs] with k hk
  let x : ℝ := (k : ℝ)^θ
  let Q : ℝ := Real.exp (-x) ^ (-α)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hceil : Q ≤ (Int.ceil Q : ℝ) := Int.le_ceil _
  change Real.exp (C * (1 + Real.log (2 * (k : ℝ))) ^ d) ≤
    (Int.ceil Q : ℝ) ^ (1/8 : ℝ)
  calc
    _ ≤ Real.exp ((α/8)*x) := Real.exp_le_exp.mpr hk
    _ = Q ^ (1/8 : ℝ) := by
      dsimp [Q]
      rw [← Real.exp_mul, ← Real.exp_mul]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow hQ.le hceil (by norm_num)

end OpenAI086.ReferenceV68
#print axioms OpenAI086.ReferenceV68.eventually_log_power_le
#print axioms OpenAI086.ReferenceV68.eventually_ceiling_overhead
