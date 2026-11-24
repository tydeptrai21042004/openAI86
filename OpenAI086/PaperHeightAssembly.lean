import Mathlib
import OpenAI086.PaperRationalMinorSelection
import OpenAI086.PaperTinyGapClosure

/-! Assemble the integer Cramer estimate with the original tiny-vector
coefficients. Column denominators may be different; their ratios must
not be silently dropped. The integer nonsingular minor is an input. -/
namespace OpenAI086

/-- If c solves the system of cleared columns, the coefficients in the
original basis are q_j c_j / Q. This recovers the missing height factor. -/
theorem v23_rescaled_cramer_l1 {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (b : I → ℤ) (c q : I → ℝ) (Q H M : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 ≤ M) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ M)
    (hd : A.det ≠ 0) (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hb : ∀ i, |(b i : ℝ)| ≤ H)
    (h : ∀ i, (∑ j, (A i j : ℝ)*c j) = (b i : ℝ)) :
    (∑ j, |q j*c j/Q|) ≤ M*((Fintype.card I : ℝ)*
      ((Fintype.card (Equiv.Perm I) : ℝ)*H^(Fintype.card I))) := by
  have hQ0 : 0 < Q := by linarith
  calc
    _ ≤ ∑ j, M*|c j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_div, abs_mul, abs_of_nonneg (hq j).1, abs_of_pos hQ0]
      apply (div_le_iff₀ hQ0).2
      calc
        q j*|c j| ≤ M*|c j| := mul_le_mul_of_nonneg_right (hq j).2 (abs_nonneg _)
        _ ≤ M*|c j|*Q := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hQ (mul_nonneg hM (abs_nonneg (c j))))
    _ = M*(∑ j, |c j|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (v22_selected_cramer_l1 A b c H hd hA hb h) hM

/-- Convert the cleared integer system to the tiny-space gap conclusion.
The equality of the real evaluation with the restored coefficients is
explicit, as is nonsingularity of the chosen integer minor. -/
theorem v23_cramer_tiny_gap {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (b : I → ℤ) (c q v : I → ℝ) (Q H M δ cutoff x : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 ≤ M) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ M)
    (hd : A.det ≠ 0) (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hb : ∀ i, |(b i : ℝ)| ≤ H)
    (h : ∀ i, (∑ j, (A i j : ℝ)*c j) = (b i : ℝ))
    (hδ : 0 ≤ δ) (hv : ∀ j, |v j| ≤ δ)
    (hx : x = ∑ j, (q j*c j/Q)*v j)
    (hsep : M*((Fintype.card I : ℝ)*
      ((Fintype.card (Equiv.Perm I) : ℝ)*H^(Fintype.card I)))*δ < cutoff)
    (hgap : |x| ≤ δ ∨ cutoff ≤ |x|) : |x| ≤ δ :=
  v19_tiny_gap_forces_small (fun j => q j*c j/Q) v δ _ cutoff x hδ hv
    (v23_rescaled_cramer_l1 A b c q Q H M hQ hM hq hd hA hb h) hx hsep hgap

/-- A nonsingular real coordinate minor remains nonsingular after actual
positive column denominator clearing. -/
theorem v23_cleared_minor_nonsingular {I : Type*} [Fintype I] [DecidableEq I]
    (a : Matrix I I ℝ) (A : Matrix I I ℤ) (q : I → ℝ)
    (h : ∀ i j, (A i j : ℝ) = a i j*q j)
    (hq : ∀ j, q j ≠ 0) (hd : a.det ≠ 0) : A.det ≠ 0 := by
  have hm : A.map (fun z : ℤ => (z : ℝ)) = a*Matrix.diagonal q := by
    ext i j
    rw [Matrix.mul_diagonal]
    exact h i j
  have hdet : (A.det : ℝ) = a.det * ∏ j, q j := by
    rw [Int.cast_det, hm, Matrix.det_mul, Matrix.det_diagonal]
  intro hz
  have hp : (∏ j, q j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hq j)
  exact (mul_ne_zero hd hp) (by simpa [hz] using hdet.symm)

/-- Assemble the actual cleared integer system and recover the bound on
original coefficients. Rational-coordinate minor selection precedes this
lemma. The numerator and denominator representations are explicitly given. -/
theorem v23_bounded_height_square_system {I : Type*} [Fintype I] [DecidableEq I]
    (a : Matrix I I ℝ) (b c : I → ℝ) (p : I → I → ℤ) (q : I → I → ℕ)
    (p₀ : I → ℤ) (q₀ : I → ℕ) (H : ℕ)
    (hp : ∀ i j, |(p i j : ℝ)| ≤ H) (hq : ∀ i j, 0 < q i j ∧ q i j ≤ H)
    (hp₀ : ∀ i, |(p₀ i : ℝ)| ≤ H) (hq₀ : ∀ i, 0 < q₀ i ∧ q₀ i ≤ H)
    (ha : ∀ i j, a i j = (p i j : ℝ)/(q i j : ℝ))
    (hb : ∀ i, b i = (p₀ i : ℝ)/(q₀ i : ℝ))
    (hd : a.det ≠ 0) (hs : ∀ i, (∑ j, a i j*c j) = b i) :
    (∑ j, |c j|) ≤ (H : ℝ)^(Fintype.card I) * ((Fintype.card I : ℝ) *
      ((Fintype.card (Equiv.Perm I) : ℝ)*((H : ℝ)^(Fintype.card I))^(Fintype.card I))) := by
  classical
  choose D hDpos hDle A hA using fun j : I =>
    v21_clear_vector_denominators (fun i => p i j) (fun i => q i j) H
      (fun i => (hq i j).1) (fun i => (hq i j).2) (fun i => hp i j)
  obtain ⟨Q,hQpos,hQle,B,hB⟩ := v21_clear_vector_denominators p₀ q₀ H
    (fun i => (hq₀ i).1) (fun i => (hq₀ i).2) hp₀
  let M : Matrix I I ℤ := Matrix.of (fun i j => A j i)
  let C : I → ℝ := fun j => (Q : ℝ)*c j/(D j : ℝ)
  have hD0 (j : I) : (D j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hDpos j))
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQpos)
  have hm (i j : I) : (M i j : ℝ) = a i j*(D j : ℝ) := by
    have h := (hA j i).1
    rw [← ha i j, mul_comm] at h
    exact h.symm
  have hdet := v23_cleared_minor_nonsingular a M (fun j => (D j : ℝ)) hm hD0 hd
  have hsys (i : I) : (∑ j, (M i j : ℝ)*C j) = (B i : ℝ) := by
    calc
      _ = ∑ j, (Q : ℝ)*(a i j*c j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hm]
        dsimp [C]
        field_simp [hD0 j] <;> ring
      _ = (Q : ℝ)*b i := by rw [← Finset.mul_sum, hs]
      _ = _ := by rw [hb]; exact (hB i).1
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
  have hDbd (j : I) : 0 ≤ (D j : ℝ) ∧ (D j : ℝ) ≤ (H : ℝ)^(Fintype.card I) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast hDle j⟩
  have h := v23_rescaled_cramer_l1 M B C (fun j => (D j : ℝ)) (Q : ℝ)
    ((H : ℝ)^(Fintype.card I)) ((H : ℝ)^(Fintype.card I)) hQ1 (by positivity) hDbd hdet
    (fun i j => (hA j i).2) (fun i => (hB i).2) hsys
  have he (j : I) : (D j : ℝ)*C j/(Q : ℝ) = c j := by
    dsimp [C]
    field_simp [hD0 j, hQ0] <;> ring
  simpa only [he] using h

end OpenAI086
