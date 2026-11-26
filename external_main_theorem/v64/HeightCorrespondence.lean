import TrilinearHT.Auto.Sec13_2TwoGraphsHeightStabilization
import SourceV64PaperExceptional

/-! An explicit correspondence between the manuscript's bounded-height
positive evaluations and the reference rational vectors. In particular
unreduced fractions do not enlarge the class of allowed evaluations. -/
namespace OpenAI086.ReferenceV64
open Auto
open scoped BigOperators

/-- Exact equality of the two height-value descriptions, at integral H. -/
theorem height_value_iff (d H : ℕ) (ξ : Fin d → ℝ) (v : ℝ) :
    OpenAI086.v34HeightValue d H ξ v ↔
      0 < v ∧ ∃ a : Fin d → ℚ, (∀ i, rationalHeight (a i) ≤ H) ∧ v = |ratEval ξ a| := by
  constructor
  · rintro ⟨hv,p,q,hp,hq,he⟩
    let a : Fin d → ℚ := fun i => (p i : ℚ) / (q i : ℚ)
    refine ⟨hv,a,?_,?_⟩
    · intro i
      have hq0 : (q i : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hq i).1)
      have hpn : (p i).natAbs ≤ H := by
        have hi : |p i| ≤ (H : ℤ) := by exact_mod_cast hp i
        exact_mod_cast (show ((p i).natAbs : ℤ) ≤ H by
          simpa only [Int.natCast_natAbs] using hi)
      have hh := rationalHeight_div_int_le (p i) (q i : ℤ) hq0
      exact (show rationalHeight (a i) ≤ max (p i).natAbs (q i) from by
        simpa [a] using hh).trans (max_le hpn (hq i).2)
    · rw [he]
      simp [OpenAI086.v34Eval, ratEval, a, Rat.cast_div]
  · rintro ⟨hv,a,ha,he⟩
    refine ⟨hv,(fun i => (a i).num),(fun i => (a i).den),?_,?_,?_⟩
    · intro i
      have hn : (a i).num.natAbs ≤ H := (le_max_left _ _).trans (ha i)
      have hz : |(a i).num| ≤ (H : ℤ) := by
        simpa only [Int.natCast_natAbs] using (show ((a i).num.natAbs : ℤ) ≤ H by exact_mod_cast hn)
      exact_mod_cast hz
    · intro i
      exact ⟨(a i).den_pos,(le_max_right _ _).trans (ha i)⟩
    · rw [he]
      unfold OpenAI086.v34Eval ratEval
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      have h := (a i).num_div_den
      exact_mod_cast h.symm

/-- The reference exceptional predicate and the paper radius predicate
are identical, not merely comparable, for an integral height threshold. -/
theorem exceptional_iff (d H K : ℕ) (ξ : Fin d → ℝ) (r T : ℝ) (b : ℤ)
    (hr : 0 < r) (hT : 0 < T) :
    Auto.ExceptionalAt ξ (H : ℝ) r T K b ↔
      OpenAI086.SourceV64.exceptionalAt d H ξ r T (K : ℤ) b := by
  constructor
  · rintro ⟨a, ha, hlo, hhi⟩
    have hv : 0 < |ratEval ξ a| := lt_trans (by positivity) hlo
    refine ⟨|ratEval ξ a|, (height_value_iff d H ξ _).mpr
      ⟨hv, a, ?_, rfl⟩, ?_, ?_⟩
    · intro i
      exact_mod_cast ha i
    · simpa [OpenAI086.v35Scale] using hlo
    · simpa [OpenAI086.v35Scale] using hhi
  · rintro ⟨v, hv, hlo, hhi⟩
    obtain ⟨_, a, ha, he⟩ := (height_value_iff d H ξ v).mp hv
    refine ⟨a, ?_, ?_, ?_⟩
    · intro i
      exact_mod_cast ha i
    · rw [he] at hlo
      simpa [OpenAI086.v35Scale] using hlo
    · rw [he] at hhi
      simpa [OpenAI086.v35Scale] using hhi

/-- Tiny-space closure on the *paper* nonexceptional blocks. The only
additional bound is the explicit numerical gap required by the reference
Cramer estimate; there is no assumed vector-level tiny closure. -/
theorem paper_tiny_closure (d H K : ℕ) (ξ : Fin d → ℝ) (r T : ℝ) (b : ℤ)
    (hr : 0 < r) (hT : 0 < T) (hH : 1 ≤ H)
    (hne : ¬OpenAI086.SourceV64.exceptionalAt d H ξ r T (K : ℤ) b)
    (hsmall : (3 * H ^ 2 : ℝ) ^ d * (d.factorial * H ^ (d ^ 2 + d)) *
      (T⁻¹ / OpenAI086.v35Scale r 1 (b - 2*(K : ℤ))) <
      T / OpenAI086.v35Scale r 1 (b + (K : ℤ)))
    (a : Fin d → ℚ) (ha : a ∈ tinySpan ξ H
      (T⁻¹ / OpenAI086.v35Scale r 1 (b - 2*(K : ℤ)))) (haH : vecHeight a ≤ H) :
    |ratEval ξ a| ≤ T⁻¹ / OpenAI086.v35Scale r 1 (b - 2*(K : ℤ)) := by
  have hneref : ¬Auto.ExceptionalAt ξ (H : ℝ) r T K b :=
    fun h => hne ((exceptional_iff d H K ξ r T b hr hT).mp h)
  apply tiny_of_mem_tinySpan ξ hH (by unfold OpenAI086.v35Scale; positivity) _ hsmall ha haH
  intro x hx
  have hxf : vecHeight x ≤ ⌊(H : ℝ)⌋₊ := by simpa using hx
  simpa [OpenAI086.v35Scale] using
    (gap_of_not_exceptionalAt (show (0 : ℝ) ≤ H by positivity) hneref x hxf)

end OpenAI086.ReferenceV64
#print axioms OpenAI086.ReferenceV64.height_value_iff
#print axioms OpenAI086.ReferenceV64.exceptional_iff

#print axioms OpenAI086.ReferenceV64.paper_tiny_closure
