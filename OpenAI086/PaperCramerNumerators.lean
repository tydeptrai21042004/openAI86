import Mathlib
import OpenAI086.PaperRationalCramerBridge

/-! Lemma 8.2: Cramer numerator bounds through replacement-column
matrices. The chosen nonsingular coordinate minor is still an input. -/
namespace OpenAI086

def v22ReplaceColumn {I : Type*} [DecidableEq I] (A : Matrix I I ℝ)
    (b : I → ℝ) (j : I) : Matrix I I ℝ := fun r s => if s = j then b r else A r s

/-- All entries of a Cramer replacement matrix obey the original height
bound, so its determinant has the same Leibniz bound. -/
theorem v22_cramer_numerator_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (b : I → ℝ) (H : ℝ) (j : I)
    (hA : ∀ r s, |A r s| ≤ H) (hb : ∀ r, |b r| ≤ H) :
    |(v22ReplaceColumn A b j).det| ≤
      (Fintype.card (Equiv.Perm I) : ℝ)*H^(Fintype.card I) := by
  apply v20_matrix_det_bound
  intro r s
  by_cases h : s = j
  · simp [v22ReplaceColumn, h, hb]
  · simp [v22ReplaceColumn, h, hA]

/-- Derive the exact Cramer determinant identity from the linear system.
Mathlib's determinant column multilinearity eliminates the old numerator
identity hypothesis. -/
theorem v22_cramer_from_system {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (b : I → ℤ) (c : I → ℝ)
    (h : ∀ i, (∑ j, (A i j : ℝ)*c j) = (b i : ℝ)) (j : I) :
    (A.det : ℝ)*c j =
      (v22ReplaceColumn (fun i k => (A i k : ℝ)) (fun i => (b i : ℝ)) j).det := by
  let M : Matrix I I ℝ := fun i k => (A i k : ℝ)
  have hcol : (fun r => ∑ k, c k • M r k) = (fun r => (b r : ℝ)) := by
    funext r
    simpa [M, smul_eq_mul, mul_comm] using h r
  have hmat : M.updateCol j (fun r => (b r : ℝ)) =
      v22ReplaceColumn M (fun r => (b r : ℝ)) j := by
    ext r k
    by_cases hk : k = j <;> simp [Matrix.updateCol, v22ReplaceColumn, hk]
  have hdet := Matrix.det_updateCol_sum M j c
  rw [hcol, hmat, smul_eq_mul] at hdet
  have hc : (A.det : ℝ) = M.det := by
    rw [Int.cast_det]
    rfl
  rw [hc, mul_comm]
  exact hdet.symm

/-- Selected minor Cramer bound after denominator clearing. The
nonsingular coordinate minor must still be selected from the basis. -/
theorem v22_selected_cramer_l1 {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (b : I → ℤ) (c : I → ℝ) (H : ℝ)
    (hd : A.det ≠ 0) (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hb : ∀ i, |(b i : ℝ)| ≤ H)
    (h : ∀ i, (∑ j, (A i j : ℝ)*c j) = (b i : ℝ)) :
    (∑ j, |c j|) ≤ (Fintype.card I : ℝ)*
      ((Fintype.card (Equiv.Perm I) : ℝ)*H^(Fintype.card I)) := by
  have hd' := v20_nonzero_integer_abs_cast A.det hd
  calc
    _ ≤ ∑ _j : I, (Fintype.card (Equiv.Perm I) : ℝ)*H^(Fintype.card I) := by
      apply Finset.sum_le_sum
      intro j _
      have hh := mul_le_mul_of_nonneg_right hd' (abs_nonneg (c j))
      rw [one_mul, ← abs_mul, v22_cramer_from_system A b c h j] at hh
      exact hh.trans (v22_cramer_numerator_bound (fun i k => (A i k : ℝ))
        (fun i => (b i : ℝ)) H j hA hb)
    _ = _ := by simp

end OpenAI086
