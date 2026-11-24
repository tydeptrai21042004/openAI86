import Mathlib

/-! Lemma 3.5: a nonzero bounded integer relation cannot have a
largest evaluation which dominates all earlier evaluations. This is the
actual scalar obstruction used after clearing the maximal minors. -/
namespace OpenAI086
open scoped BigOperators

theorem v29_dominant_integer_relation {I : Type*} [DecidableEq I]
    (s : Finset I) (j : I) (hj : j ∈ s) (a : I → ℤ) (v : I → ℝ)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) (ha : a j ≠ 0)
    (hsmall : ∀ i ∈ s.erase j, |(a i : ℝ)| ≤ H ∧ |v i| ≤ M)
    (hlarge : (s.erase j).card * H * M < |v j|) :
    (∑ i ∈ s, (a i : ℝ)*v i) ≠ 0 := by
  classical
  intro hz
  have hcast : (1 : ℝ) ≤ |(a j : ℝ)| := by
    have h : (1 : ℤ) ≤ |a j| := by
      have hp : 0 < |a j| := abs_pos.mpr ha
      omega
    exact_mod_cast h
  have hrest : |∑ i ∈ s.erase j, (a i : ℝ)*v i| ≤ (s.erase j).card * H * M := by
    calc
      _ ≤ ∑ i ∈ s.erase j, |(a i : ℝ)*v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s.erase j, H*M := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul (hsmall i hi).1 (hsmall i hi).2 (abs_nonneg _) hH
      _ = _ := by simp [mul_assoc]
  have heq : (∑ i ∈ s.erase j, (a i : ℝ)*v i) + (a j : ℝ)*v j = 0 :=
    (Finset.sum_erase_add _ _ hj).trans hz
  have he : |(a j : ℝ)*v j| = |∑ i ∈ s.erase j, (a i : ℝ)*v i| := by
    rw [show (a j : ℝ)*v j = -(∑ i ∈ s.erase j, (a i : ℝ)*v i) by linarith, abs_neg]
  have hleft : |v j| ≤ |(a j : ℝ)*v j| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcast (abs_nonneg (v j))
  linarith

/-- A single separated packet contains at most `d` selected values once
bounded-relation exclusion has established their linear independence.
The nontrivial bounded-minor construction must supply that independence. -/
theorem v29_independent_evaluation_count {I : Type*} [Fintype I]
    (d : ℕ) (v : I → Fin d → ℚ) (hv : LinearIndependent ℚ v) :
    Fintype.card I ≤ d := by
  have h := hv.fintype_card_le_finrank
  simpa using h

end OpenAI086
