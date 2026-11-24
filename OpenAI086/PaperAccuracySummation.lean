import Mathlib
import OpenAI086.PaperFinalAbsorption

/-! Section 10.4, p.93: uniform summation of the weighted accuracy
levels. We derive a quantitative finite-cutoff bound from the actual
superlinear growth of the starting logarithms. This is not the local
analytic estimate of Proposition 2.3. -/
namespace OpenAI086

/-- Multiplicity of the t-th update is at most 2^t. -/
theorem v39_level_multiplicity (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

/-- Uniform geometric bound at ratio at most 1/2. -/
theorem v39_geometric_half (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1/2) :
    (∑ j ∈ Finset.range n, r^j) ≤ 2*(1-r^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr n)
    linarith

/-- If the transformed accuracy u doubles at every level and is
nonnegative initially, then u_n >= (n+1)u_0. -/
theorem v39_accuracy_linear_lower (u : ℕ → ℝ) (h0 : 0 ≤ u 0)
    (hg : ∀ n, 2*u n ≤ u (n+1)) (n : ℕ) :
    ((n:ℝ)+1)*u 0 ≤ u n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ)*u 0 := mul_nonneg (by positivity) h0
    push_cast
    linarith [hg n]

/-- A doubling transformed log yields a weighted finite-cutoff bound
uniform in N. The factor (t+1) is the paper's O(t) multiplicity.
The large starting logarithm condition is u_0 >= 3. -/
theorem v39_accuracy_weighted_sum (u : ℕ → ℝ) (h0 : 3 ≤ u 0)
    (hg : ∀ n, 2*u n ≤ u (n+1)) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n:ℝ)+1)*Real.exp (-u n)) ≤
      2*Real.exp (-u 0) := by
  let r := Real.exp (-u 0)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr4 : r ≤ 1/4 := by
    have h : 4 ≤ Real.exp (u 0) := by linarith [Real.add_one_le_exp (u 0)]
    dsimp [r]
    rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hterm (n : ℕ) : ((n:ℝ)+1)*Real.exp (-u n) ≤ r*(2*r)^n := by
    have hu := v39_accuracy_linear_lower u (by linarith) hg n
    have hex : Real.exp (-u n) ≤ r^(n+1) := by
      have h := Real.exp_le_exp.mpr (show -u n ≤ ((n:ℝ)+1)*(-u 0) by linarith)
      have he : Real.exp (((n:ℝ)+1)*(-u 0)) = r^(n+1) := by
        rw [← Nat.cast_succ, Real.exp_nat_mul]
      rwa [he] at h
    have hn : (n:ℝ)+1 ≤ (2:ℝ)^n := by exact_mod_cast v39_level_multiplicity n
    calc
      _ ≤ ((n:ℝ)+1)*r^(n+1) := mul_le_mul_of_nonneg_left hex (by positivity)
      _ ≤ (2:ℝ)^n*r^(n+1) := mul_le_mul_of_nonneg_right hn (pow_nonneg hr _)
      _ = r*(2*r)^n := by rw [pow_succ, mul_pow]; ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, r*(2*r)^n := Finset.sum_le_sum (fun n _ => hterm n)
    _ = r*(∑ n ∈ Finset.range N, (2*r)^n) := by rw [Finset.mul_sum]
    _ ≤ r*2 := by
      apply mul_le_mul_of_nonneg_left _ hr
      have h := v39_geometric_half N (2*r) (by positivity) (by linarith)
      linarith [pow_nonneg (show 0 ≤ 2*r by positivity) N]
    _ = 2*Real.exp (-u 0) := by simp [r, mul_comm]

/-- The small-coefficient target can be achieved uniformly in cutoff
with the explicit sufficient starting bound u_0 >= max(3, 2/c).
This avoids assuming convergence or vanishing of the series. -/
theorem v39_accuracy_small_coefficient (u : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (h0 : 3 ≤ u 0) (hstart : 2/c ≤ u 0)
    (hg : ∀ n, 2*u n ≤ u (n+1)) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n:ℝ)+1)*Real.exp (-u n)) ≤ c := by
  have h := v39_accuracy_weighted_sum u h0 hg N
  have he : 2/c ≤ Real.exp (u 0) := by linarith [Real.add_one_le_exp (u 0)]
  have hh : 2 ≤ Real.exp (u 0)*c := (div_le_iff₀ hc).mp he
  have hsmall : 2*Real.exp (-u 0) ≤ c := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith)
  exact h.trans hsmall

/-- For the paper's k_{n+1}=k_n^A with A>=2, the simpler condition
k_{n+1}>=k_n^2 suffices. Transform u_n=c*k_n^theta. No analytic
parameter estimate or assumed decay of the series is used here. -/
theorem v39_power_accuracy_growth (k : ℕ → ℝ) (c θ : ℝ)
    (hc : 0 < c) (hθ : 0 < θ) (hk : 0 < k 0)
    (hstart : 2 ≤ (k 0)^θ)
    (hstep : ∀ n, (k n)^2 ≤ k (n+1)) :
    ∀ n, 2*(c*(k n)^θ) ≤ c*(k (n+1))^θ := by
  have hpos : ∀ n, 0 < k n := by
    intro n
    induction n with
    | zero => exact hk
    | succ n ih => exact (sq_pos_of_pos ih).trans_le (hstep n)
  have hp (n : ℕ) : ((k n)^θ)^2 ≤ (k (n+1))^θ := by
    have h := Real.rpow_le_rpow (sq_nonneg (k n)) (hstep n) hθ.le
    rw [pow_two, Real.mul_rpow (hpos n).le (hpos n).le] at h
    simpa [pow_two] using h
  have hlarge : ∀ n, 2 ≤ (k n)^θ := by
    intro n
    induction n with
    | zero => exact hstart
    | succ n ih => nlinarith [hp n, sq_nonneg ((k n)^θ-2)]
  intro n
  have hsq : 2*(k n)^θ ≤ ((k n)^θ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (k n)^θ from Real.rpow_nonneg (hpos n).le _) (sub_nonneg.mpr (hlarge n))]
  have h := mul_le_mul_of_nonneg_left (hsq.trans (hp n)) hc.le
  linarith

/-- Extend the finite-cutoff estimate to the nonnegative infinite sum;
ENNReal distinguishes a divergent series from a zero-valued real tsum. -/
theorem v39_accuracy_infinite (u : ℕ → ℝ) (h0 : 3 ≤ u 0)
    (hg : ∀ n, 2*u n ≤ u (n+1)) :
    (∑' n : ℕ, ENNReal.ofReal (((n:ℝ)+1)*Real.exp (-u n))) ≤
      ENNReal.ofReal (2*Real.exp (-u 0)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let N := (∑ n ∈ S, n)+1
  have hsub : S ⊆ Finset.range N := by
    intro n hn
    apply Finset.mem_range.mpr
    have hle : n ≤ ∑ j ∈ S, j := Finset.single_le_sum (fun j _ => Nat.zero_le j) hn
    exact Nat.lt_succ_of_le hle
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans
    (v39_accuracy_weighted_sum u h0 hg N)

/-- Real-series convergence and bound for the actual powered accuracy
sequence. The positive lower bound on k0 is an adjustable start choice. -/
theorem v39_paper_accuracy_series (k : ℕ → ℝ) (c θ : ℝ)
    (hc : 0 < c) (hθ : 0 < θ) (hk : 0 < k 0)
    (hstart : 2 ≤ (k 0)^θ) (hlarge : 3 ≤ c*(k 0)^θ)
    (hstep : ∀ n, (k n)^2 ≤ k (n+1)) :
    Summable (fun n : ℕ => ((n:ℝ)+1)*Real.exp (-c*(k n)^θ)) ∧
    (∑' n : ℕ, ((n:ℝ)+1)*Real.exp (-c*(k n)^θ)) ≤
      2*Real.exp (-c*(k 0)^θ) := by
  let f : ℕ → ℝ := fun n => ((n:ℝ)+1)*Real.exp (-c*(k n)^θ)
  let u : ℕ → ℝ := fun n => c*(k n)^θ
  have hpos : ∀ n, 0 ≤ f n := fun n => by dsimp [f]; positivity
  have h := v39_accuracy_infinite u hlarge
    (v39_power_accuracy_growth k c θ hc hθ hk hstart hstep)
  have he : (∑' n : ℕ, ENNReal.ofReal (f n)) ≤
      ENNReal.ofReal (2*Real.exp (-c*(k 0)^θ)) := by
    simpa [f, u, neg_mul] using h
  have hfinite : (∑' n : ℕ, ENNReal.ofReal (f n)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt he ENNReal.ofReal_lt_top)
  have hs : Summable f := by
    have hf : (fun n : ℕ => (ENNReal.ofReal (f n)).toReal) = f := by
      funext n
      exact ENNReal.toReal_ofReal (hpos n)
    rw [← hf]
    exact ENNReal.summable_toReal hfinite
  refine ⟨hs, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  rw [← ENNReal.ofReal_tsum_of_nonneg hpos hs,
    ENNReal.toReal_ofReal (tsum_nonneg hpos), ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

end OpenAI086
