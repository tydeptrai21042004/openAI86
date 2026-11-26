import OpenAI086.PaperStatement
import TrilinearHT.Theorems
import TrilinearHT.Auto.Sec16_3SummingUpdateLevels

/-! Dependency-backed replay of the locked minus-shift goal.
Reference proof: Joris Roos et al., lean-trilinearht, archive commit
7b4209609e6a7fb9d9935973ee8541495f943660 (Apache-2.0).
This file is not part of the independent OpenAI086 root. -/
noncomputable section
namespace OpenAI086.ReferenceV55
open MeasureTheory Filter Topology

theorem exact_main : Theorem1_1_Goal := by
  obtain ⟨C, hC⟩ := TrilinearHT.trilinear_ht_bound
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro f
  let Tf : ℝ → ℂ := TrilinearHT.T (fun i => f i)
  refine ⟨fun x => -Tf x, ?_, ?_⟩
  · intro x
    have hsign : (fun ε : ℝ => truncHilbert (fun i => f i) x ε) =
        (fun ε : ℝ => -TrilinearHT.T_trunc (fun i => f i) x ε) := by
      funext ε
      have h := Auto.T_trunc_eq_neg (fun i => (f i : ℝ → ℂ)) x ε
      change TrilinearHT.T_trunc (fun i => f i) x ε =
        -(truncHilbert (fun i => f i) x ε) at h
      rw [h, neg_neg]
    rw [hsign]
    exact (Auto.tendsto_T_trunc f x).neg
  · change eLpNorm (-Tf) 1 ≤ ENNReal.ofReal (max C 0) * ∏ i : Fin 3, eLpNorm (f i) 3
    rw [eLpNorm_neg]
    exact (hC f).trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (le_max_left C 0)) _)
end OpenAI086.ReferenceV55

example : OpenAI086.Theorem1_1_Goal := OpenAI086.ReferenceV55.exact_main
#print axioms TrilinearHT.trilinear_ht_bound
#print axioms Auto.T_trunc_eq_neg
#print axioms Auto.tendsto_T_trunc
#print axioms Auto.finite_inverse
#print axioms Auto.tht_main
#print axioms OpenAI086.ReferenceV55.exact_main
