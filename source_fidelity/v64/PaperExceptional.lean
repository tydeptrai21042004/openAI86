import OpenAI086.PaperV56ExceptionalBlocks
import OpenAI086.PaperHeightFinalWrappers

/-! Lemma 8.2, first clause, for the actual radii in (23) of the printed
paper. This eliminates the earlier assumption that the exceptional set
already satisfies the log-window condition. It only uses Lemma 3.5(1),
not the false dimension-free bound in Lemma 3.5(2). -/
namespace OpenAI086.SourceV64
open scoped Classical

noncomputable def exceptionalAt (d H : ℕ) (ξ : Fin d → ℝ)
    (r T : ℝ) (K b : ℤ) : Prop :=
  ∃ v, v34HeightValue d H ξ v ∧
    T⁻¹ / v35Scale r 1 (b - 2*K) < v ∧
    v < T / v35Scale r 1 (b + K)

/-- The logarithmic window in the paper follows from the actual radius
inequalities, with no assumption on the magnitudes of the frequencies. -/
theorem exceptional_log_window (d H : ℕ) (ξ : Fin d → ℝ)
    (r T : ℝ) (K b : ℤ) (hr : 0 < r) (hT : 1 ≤ T)
    (he : exceptionalAt d H ξ r T K b) :
    ∃ v, v34HeightValue d H ξ v ∧
      (b : ℝ) - 2*(K : ℝ) - Real.log T / Real.log 2 <
        Real.log v / Real.log 2 + Real.log r / Real.log 2 ∧
      Real.log v / Real.log 2 + Real.log r / Real.log 2 <
        (b : ℝ) + (K : ℝ) + Real.log T / Real.log 2 := by
  obtain ⟨v, hv, hlo, hhi⟩ := he
  have ht : 0 < T := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < v35Scale r 1 (b-2*K) := by unfold v35Scale; positivity
  have hb : 0 < v35Scale r 1 (b+K) := by unfold v35Scale; positivity
  have hlow := Real.log_lt_log (inv_pos.mpr ht) ((div_lt_iff₀ ha).mp hlo)
  have hhigh := Real.log_lt_log (mul_pos hb hv.1) ((lt_div_iff₀ hb).mp hhi)
  rw [Real.log_inv, mul_comm v, v36_log_scaled r v 1 (b-2*K) hr hv.1] at hlow
  rw [mul_comm v, v36_log_scaled r v 1 (b+K) hr hv.1] at hhigh
  push_cast at hlow hhigh
  simp only [Nat.cast_one, one_mul] at hlow hhigh
  have hL : ((b : ℝ) - 2*(K : ℝ))*Real.log 2 - Real.log T <
      Real.log v + Real.log r := by linarith
  have hU : Real.log v + Real.log r <
      ((b : ℝ) + (K : ℝ))*Real.log 2 + Real.log T := by linarith
  have hLd := div_lt_div_of_pos_right hL h2
  have hUd := div_lt_div_of_pos_right hU h2
  refine ⟨v,hv,?_,?_⟩
  · convert hLd using 1 <;> field_simp [ne_of_gt h2] <;> ring
  · convert hUd using 1 <;> field_simp [ne_of_gt h2] <;> ring

/-- Count the actual exceptional blocks by filtering an arbitrary finite
K-spaced schedule. The output is 5d as in the printed proof. -/
theorem actual_exceptional_count (d H : ℕ) (ξ : Fin d → ℝ)
    (r T : ℝ) (K b₀ : ℤ) (S : Finset ℤ)
    (hr : 0 < r) (hT : 1 ≤ T) (hK : 0 < K)
    (hw : 2*v34Width d H + 2*(Real.log T / Real.log 2) ≤ (K : ℝ)) :
    ((S.filter fun n => exceptionalAt d H ξ r T K (b₀+K*n)).card : ℝ) ≤ 5*(d:ℝ) := by
  classical
  apply v56_primary_exceptional_blocks d H ξ _ (K:ℝ)
    (Real.log T / Real.log 2) (b₀:ℝ) (Real.log r / Real.log 2)
    (by exact_mod_cast hK) (div_nonneg (Real.log_nonneg hT) (Real.log_nonneg (by norm_num))) hw
  intro n hn
  have h := exceptional_log_window d H ξ r T K (b₀+K*n) hr hT (Finset.mem_filter.mp hn).2
  push_cast at h
  exact h

end OpenAI086.SourceV64
#print axioms OpenAI086.SourceV64.exceptional_log_window
#print axioms OpenAI086.SourceV64.actual_exceptional_count
