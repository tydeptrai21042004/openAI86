import Mathlib
import OpenAI086.FiniteMultifamilyStops

/-! Corollary 5.2, p.32: tail assembly independent of the number of
retained scales, and a common catalog for all retained scale choices.
The required analytic shell estimates must be obtained from Lemma 5.1. -/
namespace OpenAI086

theorem v27_geometric_tail (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (1-r)*(∑ j ∈ Finset.range n, r^j) = 1-r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, mul_add, ih]
    ring

theorem v27_predictor_tail_bound (n B : ℕ) (r C : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hC : 0 ≤ C) (cost : ℕ → ℝ) (h : ∀ j < n, cost (B+j) ≤ C*r^(B+j)) :
    (∑ j ∈ Finset.range n, cost (B+j)) ≤ C*r^B/(1-r) := by
  have hp : 0 < 1-r := by linarith
  have hs : (∑ j ∈ Finset.range n, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ hp).2
    rw [mul_comm, v27_geometric_tail n r hr hr1]
    have hn := pow_nonneg hr n
    linarith
  calc
    _ ≤ ∑ j ∈ Finset.range n, C*r^(B+j) := Finset.sum_le_sum
      (fun j hj => h j (Finset.mem_range.mp hj))
    _ = (C*r^B)*(∑ j ∈ Finset.range n, r^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    _ ≤ (C*r^B)*(1/(1-r)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hC (pow_nonneg hr B))
    _ = _ := by ring

/-- Pool rational-frequency choices across retained chart families, not
across depth indices. All selected entries remain in this single list. -/
theorem v27_predictor_catalog {I J : Type*} [DecidableEq J]
    (families : Finset I) (entries : I → Finset J) (B : ℕ)
    (hB : ∀ i ∈ families, (entries i).card ≤ B) :
    ∃ catalog : Finset J, (∀ i ∈ families, entries i ⊆ catalog) ∧
      catalog.card ≤ families.card*B := by
  classical
  refine ⟨families.biUnion entries, ?_, ?_⟩
  · intro i hi j hj
    exact Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
  · calc
      _ ≤ ∑ i ∈ families, (entries i).card := finite_biUnion_card_le_sum families entries
      _ ≤ ∑ i ∈ families, B := Finset.sum_le_sum hB
      _ = _ := by simp [Nat.mul_comm]

end OpenAI086
