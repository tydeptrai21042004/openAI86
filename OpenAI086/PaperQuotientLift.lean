import Mathlib
import OpenAI086.PaperSaturatedLattice

/-! Lemma 8.3: a basis-free Bezout step in the saturated quotient and the
bounded representative obtained by rounding a rational spanning set. -/
namespace OpenAI086

/-- If q is coprime to L (with explicit Bezout witnesses), divisibility
of q*a modulo U implies divisibility of a modulo U. This avoids a choice
of integral basis of the quotient. -/
theorem v22_quotient_bezout_lift {I : Type*} (U : Submodule ℚ (I → ℚ))
    (a b : I → ℤ) (q L u v : ℤ) (hbez : u*q+v*L = 1)
    (h : (fun i => ((q*a i-L*b i : ℤ) : ℚ)) ∈ U) :
    ∃ c : I → ℤ, (fun i => ((a i-L*c i : ℤ) : ℚ)) ∈ U := by
  refine ⟨fun i => u*b i+v*a i, ?_⟩
  have hu := U.smul_mem (u : ℚ) h
  convert hu using 1
  funext i
  change ((a i-L*(u*b i+v*a i) : ℤ) : ℚ) =
    (u : ℚ)*((q*a i-L*b i : ℤ) : ℚ)
  have hr : (u : ℚ)*(q : ℚ)+(v : ℚ)*(L : ℚ) = 1 := by exact_mod_cast hbez
  push_cast
  linear_combination - (a i : ℚ)*hr

/-- Strip a common nonzero integer factor using saturation, then apply
Bezout. The arithmetic construction of the coprime factors is separate. -/
theorem v22_quotient_cancel_then_lift {I : Type*} (U : Submodule ℚ (I → ℚ))
    (a b : I → ℤ) (d q L u v : ℤ) (hd : d ≠ 0) (hbez : u*q+v*L=1)
    (h : (fun i => ((d*(q*a i-L*b i) : ℤ) : ℚ)) ∈ U) :
    ∃ c : I → ℤ, (fun i => ((a i-L*c i : ℤ) : ℚ)) ∈ U :=
  v22_quotient_bezout_lift U a b q L u v hbez
    (v21_rational_lattice_saturated U (fun i => q*a i-L*b i) d hd h)

/-- Rounding real coefficients leaves at most one unit of each spanning
vector. This is the paper's small-spanning-set argument, not a lattice
basis estimate. -/
theorem v22_rounding_remainder {J : Type*} [Fintype J]
    (c w : J → ℝ) (B : ℝ) (hw : ∀ j, |w j| ≤ B) :
    |∑ j, (c j-(⌊c j⌋ : ℤ))*w j| ≤ (Fintype.card J : ℝ)*B := by
  classical
  calc
    _ ≤ ∑ j, |(c j-(⌊c j⌋ : ℤ))*w j| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.univ : Finset J)
        (fun j => (c j-(⌊c j⌋ : ℤ))*w j)
    _ ≤ ∑ _j : J, B := by
      apply Finset.sum_le_sum
      intro j _
      have h0 : 0 ≤ c j-(⌊c j⌋ : ℤ) := sub_nonneg.mpr (Int.floor_le _)
      have h1 : c j-(⌊c j⌋ : ℤ) ≤ 1 := by linarith [Int.lt_floor_add_one (c j)]
      rw [abs_mul, abs_of_nonneg h0]
      calc
        _ ≤ 1*|w j| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ B := by simpa using hw j
    _ = _ := by simp

/-- The rounded lift is integral and remains in the same rational coset.
The coordinate estimate is independent of the lattice covolume. -/
theorem v22_bounded_representative {I J : Type*} [Fintype J]
    (U : Submodule ℚ (I → ℚ)) (a : I → ℤ) (w : J → I → ℤ)
    (c : J → ℝ) (target : I → ℝ) (B : ℝ)
    (hU : ∀ j, (fun i => (w j i : ℚ)) ∈ U)
    (hw : ∀ j i, |(w j i : ℝ)| ≤ B)
    (ha : ∀ i, (a i : ℝ) = target i+∑ j, c j*(w j i : ℝ)) :
    ∃ a' : I → ℤ, (fun i => ((a i-a' i : ℤ) : ℚ)) ∈ U ∧
      ∀ i, |(a' i : ℝ)-target i| ≤ (Fintype.card J : ℝ)*B := by
  classical
  let a' : I → ℤ := fun i => a i-∑ j, ⌊c j⌋*w j i
  refine ⟨a', ?_, ?_⟩
  · have hsum : (∑ j, (⌊c j⌋ : ℚ) • (fun i => (w j i : ℚ))) ∈ U :=
      U.sum_mem (fun j _ => U.smul_mem _ (hU j))
    convert hsum using 1
    funext i
    simp [a', Finset.sum_apply, Pi.smul_apply, smul_eq_mul] <;> push_cast <;> ring
  · intro i
    have he : (a' i : ℝ)-target i = ∑ j, (c j-(⌊c j⌋ : ℤ))*(w j i : ℝ) := by
      dsimp [a']
      push_cast
      rw [ha i]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [he]
    exact v22_rounding_remainder c (fun j => (w j i : ℝ)) B (fun j => hw j i)

end OpenAI086
