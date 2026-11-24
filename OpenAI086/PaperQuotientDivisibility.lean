import Mathlib
import OpenAI086.PaperQuotientLift

/-! Cancel all denominator factors that divide the power of six by
saturation, and the coprime part by Bezout. No quotient basis is needed.
The valuation decomposition of the bounded denominator remains separate. -/
namespace OpenAI086

theorem v23_power_quotient_lift {I : Type*} (U : Submodule ℚ (I → ℚ))
    (a b : I → ℤ) (d q L R u v : ℤ) (hd : d ≠ 0)
    (hbez : u*q+v*L=1)
    (h : (fun i => ((d*q*a i-d*L*R*b i : ℤ) : ℚ)) ∈ U) :
    ∃ c : I → ℤ, (fun i => ((a i-L*c i : ℤ) : ℚ)) ∈ U := by
  apply v22_quotient_cancel_then_lift U a (fun i => R*b i) d q L u v hd hbez
  convert h using 1
  funext i
  push_cast
  ring

/-- If a rational shift differs by a vector in U, changing denominator
from 6^h to 6^(h-Δ) preserves the rational coset. -/
theorem v23_shift_descends {I : Type*} (U : Submodule ℚ (I → ℚ))
    (a b : I → ℤ) (L l : ℚ) (hl : l ≠ 0) (hL : L ≠ 0)
    (h : (fun i => (a i : ℚ)-l*(b i : ℚ)) ∈ U) :
    (fun i => (a i : ℚ)/L-(b i : ℚ)/(L/l)) ∈ U := by
  have hm := U.smul_mem (1/L) h
  convert hm using 1
  funext i
  change (a i : ℚ)/L-(b i : ℚ)/(L/l) = (1/L)*((a i : ℚ)-l*(b i : ℚ))
  field_simp <;> ring

/-- The coprime Bezout witnesses are computed by Mathlib's extended gcd. -/
theorem v23_power_quotient_lift_gcd {I : Type*} (U : Submodule ℚ (I → ℚ))
    (a b : I → ℤ) (d q L R : ℤ) (hd : d ≠ 0) (hgcd : Int.gcd q L = 1)
    (h : (fun i => ((d*q*a i-d*L*R*b i : ℤ) : ℚ)) ∈ U) :
    ∃ c : I → ℤ, (fun i => ((a i-L*c i : ℤ) : ℚ)) ∈ U := by
  have hh := Int.gcd_eq_gcd_ab q L
  rw [hgcd] at hh
  apply v23_power_quotient_lift U a b d q L R (Int.gcdA q L) (Int.gcdB q L) hd _ h
  simpa only [mul_comm] using hh.symm

end OpenAI086
