import OpenAI086.PaperAccuracySummation

/-! Section 10.4: make the actual shifted, weighted infinite accuracy
series arbitrarily small. The initial log is chosen explicitly and the
recurrence is constructed, not assumed to have a small series. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

def v42Accuracy (A k : ℝ) : ℕ → ℝ
  | 0 => k
  | n+1 => Real.rpow (v42Accuracy A k n) A

theorem v42_accuracy_at_least_one (A k : ℝ) (hA : 2 ≤ A) (hk : 1 ≤ k) :
    ∀ n, 1 ≤ v42Accuracy A k n := by
  intro n
  induction n with
  | zero => exact hk
  | succ n ih =>
    change 1 ≤ Real.rpow (v42Accuracy A k n) A
    simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) ih (by linarith : 0 ≤ A)

theorem v42_accuracy_square_growth (A k : ℝ) (hA : 2 ≤ A) (hk : 1 ≤ k) :
    ∀ n, (v42Accuracy A k n)^2 ≤ v42Accuracy A k (n+1) := by
  intro n
  have h := Real.rpow_le_rpow_of_exponent_le (v42_accuracy_at_least_one A k hA hk n) hA
  change (v42Accuracy A k n)^2 ≤ Real.rpow (v42Accuracy A k n) A
  simpa only [Real.rpow_two] using h

/-- The actual multiplicity t = n+12 is handled without discarding it.
This bound is uniform in the finite cutoff and in the full infinite sum. -/
theorem v42_shifted_accuracy_tail (k : ℕ → ℝ) (c θ δ : ℝ) (m : ℕ)
    (hc : 0 < c) (hθ : 0 < θ) (hδ : 0 < δ) (hm : 0 < m)
    (hk : 0 < k 0) (hstart : 2 ≤ (k 0)^θ) (hlarge : 3 ≤ c*(k 0)^θ)
    (hsmall : 2*(m:ℝ)/δ ≤ c*(k 0)^θ)
    (hstep : ∀ n, (k n)^2 ≤ k (n+1)) :
    Summable (fun n : ℕ => ((n:ℝ)+m)*Real.exp (-c*(k n)^θ)) ∧
    (∑' n : ℕ, ((n:ℝ)+m)*Real.exp (-c*(k n)^θ)) ≤ δ := by
  obtain ⟨hs, hb⟩ := v39_paper_accuracy_series k c θ hc hθ hk hstart hlarge hstep
  have hm' : (1:ℝ) ≤ m := by
    have hm1 : 1 ≤ m := hm
    exact_mod_cast hm1
  let f : ℕ → ℝ := fun n => ((n:ℝ)+m)*Real.exp (-c*(k n)^θ)
  let g : ℕ → ℝ := fun n => (m:ℝ)*(((n:ℝ)+1)*Real.exp (-c*(k n)^θ))
  have hg : Summable g := hs.mul_left _
  have hle : ∀ n, f n ≤ g n := by
    intro n
    dsimp [f,g]
    have h : (n:ℝ)+m ≤ (m:ℝ)*((n:ℝ)+1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm') (show 0 ≤ (n:ℝ) by positivity)]
    calc
      _ ≤ ((m:ℝ)*((n:ℝ)+1))*Real.exp (-c*(k n)^θ) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by ring
  have hsf : Summable f := Summable.of_nonneg_of_le (fun n => by dsimp [f]; positivity) hle hg
  refine ⟨hsf, ?_⟩
  change (∑' n, f n) ≤ δ
  calc
    _ ≤ ∑' n, g n := tsum_le_tsum hle hsf hg
    _ = (m:ℝ)*(∑' n : ℕ, ((n:ℝ)+1)*Real.exp (-c*(k n)^θ)) := by
      simp only [g, tsum_mul_left]
    _ ≤ (m:ℝ)*(2*Real.exp (-c*(k 0)^θ)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ δ := by
      have h : 2*(m:ℝ)/δ ≤ Real.exp (c*(k 0)^θ) := by
        linarith [Real.add_one_le_exp (c*(k 0)^θ)]
      have hh := (div_le_iff₀ hδ).mp h
      rw [Real.exp_neg]
      calc
        _ = (2*(m:ℝ))/Real.exp (c*(k 0)^θ) := by ring
        _ ≤ δ := (div_le_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hh)

/-- Existence of arbitrarily large initial logarithms, with the explicit
power recurrence and the small infinite coefficient of the paper. -/
theorem v42_choose_accuracy_start (A c θ δ K : ℝ) (m : ℕ)
    (hA : 2 ≤ A) (hc : 0 < c) (hθ : 0 < θ) (hδ : 0 < δ) (hm : 0 < m) :
    ∃ k : ℝ, K ≤ k ∧ 1 ≤ k ∧
      Summable (fun n : ℕ => ((n:ℝ)+m)*Real.exp (-c*(v42Accuracy A k n)^θ)) ∧
      (∑' n : ℕ, ((n:ℝ)+m)*Real.exp (-c*(v42Accuracy A k n)^θ)) ≤ δ := by
  let M := max 2 (max (3/c) ((2*(m:ℝ)/δ)/c))
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_left _ _)
  let k := max (max K 1) (Real.rpow M θ⁻¹)
  have hk1 : 1 ≤ k := (le_max_right K 1).trans (le_max_left _ _)
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one hk1
  have hp : M ≤ k^θ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hM.le _) (le_max_right (max K 1) (Real.rpow M θ⁻¹)) hθ.le
    rw [← Real.rpow_mul hM.le, inv_mul_cancel₀ hθ.ne', Real.rpow_one] at h
    exact h
  have h2 : 2 ≤ k^θ := (le_max_left _ _).trans hp
  have h3 : 3 ≤ c*k^θ := by
    have h : 3/c ≤ k^θ := (le_max_left _ _).trans ((le_max_right _ _).trans hp)
    simpa [mul_comm] using (div_le_iff₀ hc).mp h
  have hd : 2*(m:ℝ)/δ ≤ c*k^θ := by
    have h : (2*(m:ℝ)/δ)/c ≤ k^θ := (le_max_right _ _).trans ((le_max_right _ _).trans hp)
    simpa [mul_comm] using (div_le_iff₀ hc).mp h
  refine ⟨k,(le_max_left K 1).trans (le_max_left _ _),hk1,?_⟩
  exact v42_shifted_accuracy_tail (v42Accuracy A k) c θ δ m hc hθ hδ hm hk h2 h3 hd
    (v42_accuracy_square_growth A k hA hk1)

end OpenAI086
