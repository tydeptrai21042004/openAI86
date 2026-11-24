import Mathlib

/-! Lemma 8.3: the integral points in a rational linear subspace are
saturated. Quotient freeness and a bounded representative lift are distinct
obligations, not consequences asserted here. -/
namespace OpenAI086

/-- Saturation for integer vectors mapped to rational coordinate space. -/
theorem v21_rational_lattice_saturated {I : Type*}
    (U : Submodule ℚ (I → ℚ)) (a : I → ℤ) (n : ℤ) (hn : n ≠ 0)
    (h : (fun i => ((n*a i : ℤ) : ℚ)) ∈ U) :
    (fun i => (a i : ℚ)) ∈ U := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hh := U.smul_mem ((n : ℚ)⁻¹) h
  convert hh using 1
  funext i
  change (a i : ℚ) = (n : ℚ)⁻¹ * ((n*a i : ℤ) : ℚ)
  push_cast
  field_simp

/-- The same fact for the difference of two lifts. -/
theorem v21_saturated_difference {I : Type*}
    (U : Submodule ℚ (I → ℚ)) (a b : I → ℤ) (n : ℤ) (hn : n ≠ 0)
    (h : (fun i => ((n*(a i-b i) : ℤ) : ℚ)) ∈ U) :
    (fun i => (a i : ℚ)-(b i : ℚ)) ∈ U := by
  simpa only [Int.cast_sub] using v21_rational_lattice_saturated U (fun i => a i-b i) n hn h

end OpenAI086
