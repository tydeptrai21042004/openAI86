import Mathlib
import OpenAI086.FiniteMultifamilyStops

/-! Lemma 3.5(2) has an omitted dimension factor. The log-coordinate
counterexample below is exact. The corrected covering estimate is stated
for actual integer scales; rational packet construction is separate. -/
namespace OpenAI086
open scoped BigOperators

def v31LogWindow (v n L : ℤ) : Prop := 0 ≤ v - n ∧ v - n ≤ L

/-- Two values of logarithmic magnitudes 0 and 3L give disjoint scale
windows, each containing L+1 integers. They correspond to the rational
coordinate evaluations of (1, 2^(3L)) at height 2. -/
theorem v31_two_scale_windows (L : ℕ) (hL : 0 < L) :
    ∃ S : Finset ℤ, S.card = 2 * (L+1) ∧
      ∀ n ∈ S, v31LogWindow 0 n L ∨ v31LogWindow (3*(L:ℤ)) n L := by
  let A := Finset.Icc (-(L:ℤ)) 0
  let B := Finset.Icc (2*(L:ℤ)) (3*(L:ℤ))
  have hA : A.card = L+1 := by
    dsimp [A]
    rw [Int.card_Icc]
    omega
  have hB : B.card = L+1 := by
    dsimp [B]
    rw [Int.card_Icc]
    omega
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro n ha hb
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    omega
  refine ⟨A ∪ B, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hd, hA, hB]; omega
  · intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · left
      have h := Finset.mem_Icc.mp hn
      unfold v31LogWindow
      omega
    · right
      have h := Finset.mem_Icc.mp hn
      unfold v31LogWindow
      omega

/-- No fixed additive constant can give the printed coefficient one in
front of the logarithmic annulus width, even for d=B=2. -/
theorem v31_no_dimension_free_width (K : ℕ) :
    ∃ L : ℕ, ∃ S : Finset ℤ,
      K+L+1 < S.card ∧
      ∀ n ∈ S, v31LogWindow 0 n L ∨ v31LogWindow (3*(L:ℤ)) n L := by
  obtain ⟨S, hS, hs⟩ := v31_two_scale_windows (K+1) (by omega)
  exact ⟨K+1, S, by omega, hs⟩

/-- The integer points of a real interval have cardinal at most width+1.
Using rounded endpoints rather than a bounded search range is essential. -/
theorem v31_real_interval_integer_count (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Icc (Int.ceil a) (Int.floor b)).card : ℝ) ≤ b-a+1 := by
  rw [Int.card_Icc]
  have heq : Int.floor b - Int.ceil a + 1 = Int.floor b + 1 - Int.ceil a := by omega
  try simp only [heq]
  have hlo : a ≤ (Int.ceil a : ℝ) := Int.le_ceil a
  have hhi : (Int.floor b : ℝ) ≤ b := Int.floor_le b
  by_cases h : 0 ≤ Int.floor b + 1 - Int.ceil a
  · have hz : (((Int.floor b + 1 - Int.ceil a).toNat : ℕ) : ℤ) =
        Int.floor b + 1 - Int.ceil a := Int.toNat_of_nonneg h
    have hzR : (((Int.floor b + 1 - Int.ceil a).toNat : ℕ) : ℝ) =
        (Int.floor b : ℝ) + 1 - (Int.ceil a : ℝ) := by exact_mod_cast hz
    rw [hzR]
    linarith
  · have hz : (Int.floor b + 1 - Int.ceil a).toNat = 0 := by omega
    rw [hz, Nat.cast_zero]
    linarith

/-- Corrected integer-scale estimate, with the width paid once per packet.
This applies to every finite subset of scales, hence to the entire set by
the finite cover. The input intervals are in log-base-two coordinates. -/
theorem v31_corrected_packet_count {I : Type*} (P : Finset I)
    (a b : I → ℝ) (W U : ℝ) (S : Finset ℤ)
    (hW : 0 ≤ W) (hU : 0 ≤ U)
    (hab : ∀ i ∈ P, a i ≤ b i)
    (hw : ∀ i ∈ P, b i-a i ≤ W+U)
    (hcover : ∀ n ∈ S, ∃ i ∈ P, a i ≤ (n:ℝ) ∧ (n:ℝ) ≤ b i) :
    (S.card : ℝ) ≤ (P.card : ℝ)*(W+U+1) := by
  classical
  let F (i : I) := Finset.Icc (Int.ceil (a i)) (Int.floor (b i))
  have hs : S ⊆ P.biUnion F := by
    intro n hn
    obtain ⟨i, hi, ha, hb⟩ := hcover n hn
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Int.ceil_le.mpr ha
    · exact Int.le_floor.mpr hb
  have hc : (S.card : ℝ) ≤ ∑ i ∈ P, ((F i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hs).trans (finite_biUnion_card_le_sum P F)
  calc
    _ ≤ ∑ i ∈ P, ((F i).card : ℝ) := hc
    _ ≤ ∑ _i ∈ P, (W+U+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := v31_real_interval_integer_count (a i) (b i) (hab i hi)
      dsimp [F]
      linarith [hw i hi]
    _ = _ := by simp

end OpenAI086
