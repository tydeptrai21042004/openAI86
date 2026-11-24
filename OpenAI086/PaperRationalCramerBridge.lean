import Mathlib
import OpenAI086.PaperRationalHeightBounds

/-! Clearing denominators in one bounded-height rational vector and the
adjugate bridge for a selected nonsingular integer minor (Lemma 8.2).
The selection of the minor from an independent rational family is separate. -/
namespace OpenAI086

/-- Explicit common denominator, without reducing fractions. The numerator
of each coordinate uses the product of all other denominators. -/
theorem v21_clear_vector_denominators {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℤ) (q : I → ℕ) (H : ℕ)
    (hq : ∀ i, 0 < q i) (hqH : ∀ i, q i ≤ H)
    (hp : ∀ i, |(p i : ℝ)| ≤ H) :
    ∃ Q : ℕ, 0 < Q ∧ Q ≤ H^(Fintype.card I) ∧
      ∃ a : I → ℤ, ∀ i, (Q : ℝ)*((p i : ℝ)/(q i : ℝ)) = (a i : ℝ) ∧
        |(a i : ℝ)| ≤ (H : ℝ)^(Fintype.card I) := by
  classical
  let Q := ∏ i, q i
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => hq i)
  have hQH : Q ≤ H^(Fintype.card I) := by
    calc
      Q ≤ ∏ _i : I, H := Finset.prod_le_prod' (fun i _ => hqH i)
      _ = _ := by simp
  refine ⟨Q, hQ, hQH, fun i => p i * (↑(∏ j ∈ Finset.univ.erase i, q j) : ℤ), ?_⟩
  intro i
  have he : (∏ j ∈ Finset.univ.erase i, q j)*q i = Q := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have her : (↑(∏ j ∈ Finset.univ.erase i, q j) : ℝ)*(q i : ℝ) = Q := by exact_mod_cast he
  have hqi : (q i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hq i))
  constructor
  · push_cast
    rw [← her]
    field_simp [hqi] <;> ring
  · push_cast
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (H : ℝ)*(↑(∏ j ∈ Finset.univ.erase i, q j) : ℝ) :=
        mul_le_mul_of_nonneg_right (hp i) (Nat.cast_nonneg _)
      _ ≤ (H : ℝ)*(∏ _j ∈ Finset.univ.erase i, (H : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        push_cast
        exact Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) (fun j _ => by exact_mod_cast hqH j)
      _ = (H : ℝ)^(Fintype.card I) := by
        have hh : (Finset.univ.erase i).card + 1 = Fintype.card I := by simp
        rw [Finset.prod_const, ← hh, pow_succ, mul_comm]

/-- Real coefficients solving an integer linear system have integer Cramer
numerators. This uses the actual adjugate identity, not an assumed division
bound. The integer determinant need not be positive. -/
theorem v21_adjugate_cramer {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (b : I → ℤ) (c : I → ℝ)
    (h : ∀ i, (∑ j, (A i j : ℝ)*c j) = (b i : ℝ)) :
    ∀ i, (A.det : ℝ)*c i = ((A.adjugate.mulVec b i : ℤ) : ℝ) := by
  classical
  intro i
  have hadj : A.adjugate * A = A.det • (1 : Matrix I I ℤ) := Matrix.adjugate_mul A
  have hentry (j : I) : (∑ k, (A.adjugate i k : ℝ)*(A k j : ℝ)) =
      if i = j then (A.det : ℝ) else 0 := by
    have hh := congrArg (fun M : Matrix I I ℤ => M i j) hadj
    simp [Matrix.mul_apply, Matrix.one_apply] at hh
    by_cases hij : i = j <;> simp [hij] at hh ⊢ <;> exact_mod_cast hh
  symm
  calc
    ((A.adjugate.mulVec b i : ℤ) : ℝ) = ∑ k, (A.adjugate i k : ℝ)*(b k : ℝ) := by
      simp [Matrix.mulVec, dotProduct]
    _ = ∑ k, (A.adjugate i k : ℝ)*(∑ j, (A k j : ℝ)*c j) := by simp only [h]
    _ = ∑ j, (∑ k, (A.adjugate i k : ℝ)*(A k j : ℝ))*c j := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = (A.det : ℝ)*c i := by simp [hentry, ite_mul]

/-- Coefficient bound with an explicit bound on the adjugate numerators. -/
theorem v21_integer_system_l1 {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (b : I → ℤ) (c : I → ℝ) (M : ℝ)
    (hd : A.det ≠ 0) (h : ∀ i, (∑ j, (A i j : ℝ)*c j) = (b i : ℝ))
    (hnum : ∀ i, |((A.adjugate.mulVec b i : ℤ) : ℝ)| ≤ M) :
    (∑ i, |c i|) ≤ (Fintype.card I : ℝ)*M :=
  v20_cramer_ratio_l1 A.det hd (A.adjugate.mulVec b) c M (v21_adjugate_cramer A b c h) hnum

end OpenAI086
