import Mathlib
import OpenAI086.OuterStopping

/-! Section 10: finite-cutoff absorption and uniform restart accounting.
The analytic estimates which produce `q`, `A`, `b`, and the level bounds
are explicit inputs. No claim of the main singular integral theorem. -/
namespace OpenAI086

/-- Uniform finite geometric bound, proved by induction. -/
theorem v24_geometric_quarter (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1/4) :
    (∑ j ∈ Finset.range n, r^j) ≤ (4/3 : ℝ)*(1-r^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h : r^n*r ≤ r^n/4 := by
      exact (mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr n)).trans_eq (by ring)
    linarith

/-- Restart roots have total length at most 4/3 of the initial length. -/
theorem v24_restart_packing (n : ℕ) (R : ℝ) (m : ℕ → ℝ) (hR : 0 ≤ R)
    (hm : ∀ j < n, m j ≤ (1/4 : ℝ)^j*R) :
    (∑ j ∈ Finset.range n, m j) ≤ (4/3 : ℝ)*R := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, (1/4 : ℝ)^j*R :=
      Finset.sum_le_sum fun j hj => hm j (Finset.mem_range.mp hj)
    _ = (∑ j ∈ Finset.range n, (1/4 : ℝ)^j)*R := by rw [Finset.sum_mul]
    _ ≤ (4/3 : ℝ)*R := by
      apply mul_le_mul_of_nonneg_right _ hR
      have h := v24_geometric_quarter n (1/4) (by norm_num) (by norm_num)
      have hn : 0 ≤ (1/4 : ℝ)^n := by positivity
      linarith

/-- Finite level expansion with a total small coefficient of C_N. The same
uniform bound survives every finite cutoff. -/
theorem v24_level_absorption {I : Type*} (s : Finset I)
    (C A B b : ℝ) (cost a : I → ℝ) (hC : 0 ≤ C)
    (hb : b ≤ 1/2) (ha : (∑ i ∈ s, a i) ≤ b)
    (hcost : ∀ i ∈ s, cost i ≤ a i*(1+C))
    (hbase : C ≤ A+B+∑ i ∈ s, cost i) :
    C ≤ 2*(A+B+b) := by
  have hs : (∑ i ∈ s, cost i) ≤ b*(1+C) := calc
    _ ≤ ∑ i ∈ s, a i*(1+C) := Finset.sum_le_sum hcost
    _ = (∑ i ∈ s, a i)*(1+C) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) hC]

end OpenAI086
