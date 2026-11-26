import TrilinearHT.Auto.Sec13_2TwoGraphsHeightStabilization

/-! Paper Lemma 8.2 on the actual reference mode schedule. Both clauses
are derived from the schedule's numerical conditions, with the exceptional
set constructed by filtering the supplied finite path of block indices.
This is a reference-dependent candidate, not an independent kernel certificate. -/
namespace OpenAI086.ReferenceV62
open Auto

open Classical in
theorem exceptional_schedule {S : ModeSchedule} {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCT : 4 ≤ CT)
    (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar)
    (hQ : 1 ≤ S.Q0) {d : ℕ} (hd : d ≤ S.dmax)
    (hW : 8 * ((d : ℝ) + 1)^3 * Real.log (2 * S.H) / Real.log 2 ≤ W)
    (Θ : Fin d → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (b0 : ℤ) (Bs : Finset ℤ) :
    ((Bs.filter fun j => ExceptionalAt Θ S.H r0 S.T S.K (b0 + j * S.K)).card ≤
      4 * S.dmax) ∧
    (∀ b : ℤ, ¬ExceptionalAt Θ S.H r0 S.T S.K b →
      ∀ a : Fin d → ℚ, vecHeight a ≤ ⌊S.H⌋₊ →
        a ∈ tinySpan Θ ⌊S.H⌋₊ (S.T⁻¹ / (r0 * (2 : ℝ)^(-(b - 2 * S.K)))) →
        |ratEval Θ a| ≤ S.T⁻¹ / (r0 * (2 : ℝ)^(-(b - 2 * S.K)))) := by
  constructor
  · exact (S.exceptional_blocks_le hV hd2 hD hB hQ hW Θ hr0 b0 _
      (fun j hj => (Finset.mem_filter.mp hj).2)).trans (Nat.mul_le_mul_left 4 hd)
  · intro b hne a haH ha
    have hH := hV.two_le_H hd2 hD hB hQ
    have hHn : 1 ≤ ⌊S.H⌋₊ := Nat.le_floor (by linarith)
    have hT := hV.one_le_T (show 1 ≤ CT by omega) hd2 hD hB hQ
    have hε : 0 ≤ S.T⁻¹ / (r0 * (2 : ℝ)^(-(b - 2 * S.K))) := by positivity
    exact tiny_of_mem_tinySpan Θ hHn hε (gap_of_not_exceptionalAt (by linarith) hne)
      (hV.tinySpan_small hCT hd2 hD hB hQ hd hr0 b) ha haH

end OpenAI086.ReferenceV62
#print axioms OpenAI086.ReferenceV62.exceptional_schedule
#print axioms Auto.ModeSchedule.exceptional_blocks_le
#print axioms Auto.tiny_of_mem_tinySpan
#print axioms Auto.ModeSchedule.Valid.tinySpan_small
