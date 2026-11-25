import OpenAI086.PaperHeightFinalWrappers
import OpenAI086.PaperLemma33Submodules
import OpenAI086.PaperAttemptTreePacking

/-! V41: paper-facing assembly of the corrected scalar height lemma.
The explicit width is the one proved by the existing rational-height machinery.
These are source candidates until Lake checks the full dependency closure. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- All three scalar conclusions, with the corrected scale-count term and
with convergence of the actual infinite tail. The dimension and frequency
vector are unrestricted. -/
def V41ScalarHeightGoal (d B : ℕ) (ξ : Fin d → ℝ) : Prop :=
  (∃ P : Finset ℝ, P.card ≤ d ∧
    ∀ v, v34HeightValue d B ξ v →
      ∃ p ∈ P, |Real.log v / Real.log 2 - p| ≤ v34Width d B) ∧
  ((v34HeightBins d B ξ).card : ℝ) ≤ (d : ℝ) * (2 * v34Width d B + 2) ∧
  (∀ (r α β : ℝ) (l : ℕ), 0 < r → 0 < α → α ≤ β → 0 < l →
    {n : ℤ | ∃ v ∈ v34Values d B ξ,
      α ≤ v35Scale r l n * v ∧ v35Scale r l n * v ≤ β}.Finite ∧
    ((v36Qualifying (v34Values d B ξ) r α β l).card : ℝ) ≤
      (d : ℝ) * ((2 * v34Width d B + (Real.log β - Real.log α) / Real.log 2) / (l : ℝ) + 1)) ∧
  (∀ (r ε : ℝ) (l : ℕ), 0 < r → 0 ≤ ε → (l = 1 ∨ l = 2) →
    Summable (v35TailMax (v34Values d B ξ) r l ε) ∧
    (∑' n : ℤ, v35TailMax (v34Values d B ξ) r l ε n) ≤
      (d : ℝ) * (2 * v34Width d B + 2) * (4 * ε))

theorem v41_scalar_height_assembly (d B : ℕ) (ξ : Fin d → ℝ) :
    V41ScalarHeightGoal d B ξ := by
  refine ⟨v34_height_log_cover d B ξ, v34_height_bin_count d B ξ, ?_, ?_⟩
  · intro r α β l hr hα hab hl
    refine ⟨?_, v36_actual_qualifying_count d B l ξ r α β hr hα hab hl⟩
    exact v36_qualifying_finite (v34Values d B ξ) r α β l
      (fun v hv => ((v34_mem_values d B ξ v).mp hv).1) hr hα hab hl
  · intro r ε l hr he hl
    exact v35_height_real_tail d B ξ r ε l hr he hl

/-- A convenient explicit upper bound for the bin-count coefficient in the
scalar lemma. No scale cutoff or bound on the frequencies is added. -/
theorem v41_height_bin_explicit (d B : ℕ) (ξ : Fin d → ℝ)
    (hd : 1 ≤ d) (hB : 2 ≤ B) :
    ((v34HeightBins d B ξ).card : ℝ) ≤
      (d : ℝ) * (8 * ((d : ℝ)+1)^2 * (Real.log (2*(B:ℝ))/Real.log 2) + 2) := by
  apply (v34_height_bin_count d B ξ).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  linarith [v35_height_width_bound d B hd hB]

/-- The explicit two-window obstruction is kept as a negative result.
It is not replaced by a proof of the printed, false coefficient. -/
theorem v41_printed_width_obstruction (K : ℕ) :
    ∃ L : ℕ, ∃ S : Finset ℤ, K+L+1 < S.card ∧
      ∀ n ∈ S, v31LogWindow 0 n L ∨ v31LogWindow (3*(L:ℤ)) n L :=
  v31_no_dimension_free_width K

end OpenAI086
