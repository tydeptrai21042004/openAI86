import OpenAI086.PaperV43Packing
import OpenAI086.PaperCompressionVectorRows

/-! Assemble the quantitative row estimates in Lemma 3.4, p.13.
This is conditional on the actual anchor/size-segment estimates. It
eliminates the generation count from the two sums, but does not construct
those estimates or prove the full compression theorem. -/
namespace OpenAI086
open scoped BigOperators

/-- Finite row costs, indexed by their unique size segment and restart
attempt, can be summed without paying for unused pairs of indices. -/
theorem v46_sum_by_owner {R K : Type*} [Fintype R] [Fintype K]
    (owner : R → K) (f : R → ℝ) :
    (∑ k, ∑ r ∈ Finset.univ.filter (fun r => owner r = k), f r) = ∑ r, f r := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single (owner r)]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

/-- The squared row norm is bounded by twice each of its two constituent
squared norms. Works for dependent row spaces. -/
theorem v46_row_split {R : Type*} [Fintype R]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (a e : (r : R) → Y r) :
    (∑ r, ‖a r + e r‖^2) ≤ 2*(∑ r, ‖a r‖^2)+2*(∑ r, ‖e r‖^2) := by
  calc
    _ ≤ ∑ r, (2*‖a r‖^2+2*‖e r‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      have h := norm_add_le (a r) (e r)
      have hs : ‖a r + e r‖^2 ≤ (‖a r‖+‖e r‖)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h)
          (show 0 ≤ ‖a r‖+‖e r‖+‖a r+e r‖ by positivity)]
      nlinarith [sq_nonneg (‖a r‖-‖e r‖)]
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Sum the anchor and coefficient-error bounds once per actual row,
then once per attempt, using the two independent attempt budgets.
Energy is the squared L² norm of the segment representative, mass is
the length-weighted square of its stopping average. -/
theorem v46_segment_row_bound {R A : Type*} [Fintype R] [Fintype A]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (owner : R → A) (anchor err : (r : R) → Y r)
    (energy mass : A → ℝ) (E M U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hE : (∑ i, energy i) ≤ 2*E) (hM : (∑ i, mass i) ≤ 2*M)
    (ha : ∀ i, (∑ r ∈ Finset.univ.filter (fun r => owner r = i), ‖anchor r‖^2) ≤ U*energy i)
    (he : ∀ i, (∑ r ∈ Finset.univ.filter (fun r => owner r = i), ‖err r‖^2) ≤ V*mass i) :
    (∑ r, ‖anchor r+err r‖^2) ≤ 4*U*E+4*V*M := by
  classical
  have h1 : (∑ r, ‖anchor r‖^2) ≤ U*(2*E) := by
    rw [← v46_sum_by_owner owner (fun r => ‖anchor r‖^2)]
    calc
      _ ≤ ∑ i, U*energy i := Finset.sum_le_sum (fun i _ => ha i)
      _ = U*(∑ i, energy i) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hU
  have h2 : (∑ r, ‖err r‖^2) ≤ V*(2*M) := by
    rw [← v46_sum_by_owner owner (fun r => ‖err r‖^2)]
    calc
      _ ≤ ∑ i, V*mass i := Finset.sum_le_sum (fun i _ => he i)
      _ = V*(∑ i, mass i) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hM hV
  have hh := v46_row_split anchor err
  linarith

/-- Final global square estimate after summing the size segments. L is
the high-root multiplicity bound. The exponent -17 in the squared error
comes from tau=D^-10 and the pathwise column energy D^3. -/
theorem v46_global_compression_budget {K : Type*} [Fintype K]
    (rowEnergy repEnergy avgEnergy : K → ℝ) (D L U Z : ℝ)
    (hD : 2 ≤ D) (hU : 0 ≤ U)
    (hrep : (∑ k, repEnergy k) ≤ (8*D⁻¹^2+L)*Z^2)
    (havg : (∑ k, avgEnergy k) ≤ (16/3)*Z^2)
    (hrow : ∀ k, rowEnergy k ≤ 4*U*repEnergy k+4*(D⁻¹)^20*D^3*avgEnergy k) :
    (∑ k, rowEnergy k) ≤ (4*U*(8*D⁻¹^2+L)+(64/3)*(D⁻¹)^17)*Z^2 := by
  have hd : D ≠ 0 := by linarith
  have hpow : (D⁻¹)^20*D^3 = (D⁻¹)^17 := by
    rw [show (20:ℕ) = 17+3 by norm_num, pow_add]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hd, one_pow, mul_one]
  have hsum : (∑ k, rowEnergy k) ≤ 4*U*(∑ k, repEnergy k)+
      4*(D⁻¹)^17*(∑ k, avgEnergy k) := by
    calc
      _ ≤ ∑ k, (4*U*repEnergy k+4*(D⁻¹)^17*avgEnergy k) := by
        apply Finset.sum_le_sum
        intro k _
        have hh : 4*(D⁻¹)^20*D^3 = 4*(D⁻¹)^17 := by
          rw [mul_assoc, hpow]
        simpa only [hh] using hrow k
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  calc
    _ ≤ _ := hsum
    _ ≤ 4*U*((8*D⁻¹^2+L)*Z^2)+4*(D⁻¹)^17*((16/3)*Z^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hrep (by positivity))
        (mul_le_mul_of_nonneg_left havg (by positivity))
    _ = _ := by ring

end OpenAI086
