import Mathlib
import OpenAI086.GenericDyadicGroups
import OpenAI086.FiniteAdaptiveRowBessel

/-! V19: dimension-free dyadic prefix bound. Only the Pythagorean
energy identity and contraction of a cumulative family are required.
Rows may take values in different normed spaces. -/
namespace OpenAI086

/-- Cumulative projection energy telescopes for every aligned block grid. -/
theorem v19_aligned_energy {X : Type*} [NormedAddCommGroup X]
    (F : ℕ → X) (hF : ∀ a b, a ≤ b →
      ‖F b - F a‖^2 = ‖F b‖^2 - ‖F a‖^2)
    (w count : ℕ) :
    (∑ j ∈ Finset.range count, ‖F ((j+1)*w) - F (j*w)‖^2) =
      ‖F (count*w)‖^2 - ‖F 0‖^2 := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Finset.sum_range_succ, ih, hF _ _ (Nat.mul_le_mul_right w (Nat.le_succ count))]
    ring

/-- Group rows by their chosen block, allowing different row codomains
and an arbitrary common row-energy constant. -/
theorem v19_masked_row_energy {X : Type*} [NormedAddCommGroup X]
    {R J : Type*} [Fintype R] [Fintype J]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (B : (r : R) → X → Y r) (C E : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ C * ‖x‖^2)
    (hzero : ∀ r, B r 0 = 0)
    (S : J → X) (j : R → J) (active : R → Bool)
    (hS : (∑ b, ‖S b‖^2) ≤ E) :
    (∑ r, ‖B r (if active r then S (j r) else 0)‖^2) ≤ C*E := by
  classical
  calc
    _ = ∑ r, ∑ b, if b = j r ∧ active r = true then ‖B r (S b)‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      cases h : active r <;> simp [h, hzero]
    _ = ∑ b, ∑ r, if b = j r ∧ active r = true then ‖B r (S b)‖^2 else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b, ∑ r, ‖B r (S b)‖^2 := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro r _
      split_ifs <;> simp [sq_nonneg]
    _ ≤ ∑ b, C*‖S b‖^2 := Finset.sum_le_sum (fun b _ => hrow (S b))
    _ ≤ C*E := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hS hC

/-- Cauchy--Schwarz over levels in arbitrary normed row codomains. -/
theorem v19_normed_level_energy {R L : Type*} [Fintype R] [Fintype L]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (A : (r : R) → L → Y r) (E : ℝ)
    (hA : ∀ l, (∑ r, ‖A r l‖^2) ≤ E) :
    (∑ r, ‖∑ l, A r l‖^2) ≤ (Fintype.card L : ℝ)^2*E := by
  classical
  calc
    _ ≤ ∑ r, (∑ l, ‖A r l‖)^2 := by
      apply Finset.sum_le_sum
      intro r _
      have h := norm_sum_le (Finset.univ : Finset L) (A r)
      have hn : 0 ≤ ‖∑ l, A r l‖ := norm_nonneg _
      have hs : 0 ≤ ∑ l, ‖A r l‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      exact pow_le_pow_left₀ hn h 2
    _ ≤ _ := finite_level_row_square_bound (fun l r => ‖A r l‖) E hA

/-- Actual prefix bound in a normed group with a cumulative energy law.
No block selector or binary decomposition is a premise. -/
theorem v19_normed_one_layer {X : Type*} [NormedAddCommGroup X]
    {R : Type*} [Fintype R] {Y : R → Type*}
    [∀ r, NormedAddCommGroup (Y r)]
    (F : ℕ → X) (hzero : F 0 = 0)
    (hF : ∀ a b, a ≤ b → ‖F b-F a‖^2 = ‖F b‖^2-‖F a‖^2)
    (E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (htop : ∀ n, ‖F n‖^2 ≤ E)
    (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ C*‖x‖^2)
    (N : R → ℕ) (k : ℕ) (hN : ∀ r, N r ≤ 2^k) :
    (∑ r, ‖B r (F (N r))‖^2) ≤ (k+1 : ℝ)^2*(C*E) := by
  classical
  let W := {w : ℕ // w ∈ finiteDyadicWidthSet k}
  letI : Fintype W := Fintype.ofFinset (finiteDyadicWidthSet k).attach (by intro w; simp)
  let A : R → W → X := fun r w => v19Grouped (v19BlockPairs F k 0 (N r)) w.val
  have hprefix (r : R) : (∑ w : W, A r w) = F (N r) := by
    have h := v19_width_prefix F k (N r) (hN r)
    rw [hzero, sub_zero] at h
    change (∑ w ∈ (finiteDyadicWidthSet k).attach,
      v19Grouped (v19BlockPairs F k 0 (N r)) w.val) = _
    simpa only [Finset.sum_attach] using h
  have hlevel (w : W) : (∑ r, ‖B r (A r w)‖^2) ≤ C*E := by
    have hex (r : R) := v19_width_choice F k (N r) w.val (hN r)
    choose active j hj using hex
    let S : Fin (2^k) → X := fun b => F ((b.val+1)*w.val) - F (b.val*w.val)
    have hS : (∑ b, ‖S b‖^2) ≤ E := by
      have h := v19_aligned_energy F hF w.val (2^k)
      simp [hzero] at h
      have hh := htop ((2^k)*w.val)
      simp only [S, Fin.sum_univ_eq_sum_range]
      exact h.le.trans hh
    have hb := v19_masked_row_energy (fun r x => B r x) C E hC hrow
      (fun r => map_zero (B r)) S j active hS
    change (∑ r, ‖B r (v19Grouped (v19BlockPairs F k 0 (N r)) w.val)‖^2) ≤ C*E
    simp_rw [hj]
    exact hb
  have h := v19_normed_level_energy (fun r w => B r (A r w)) (C*E) hlevel
  have heq (r : R) : (∑ w : W, B r (A r w)) = B r (F (N r)) := by
    rw [← map_sum, hprefix]
  simp_rw [heq] at h
  have hc : Fintype.card W ≤ k+1 := by
    change (finiteDyadicWidthSet k).attach.card ≤ k+1
    simpa using finite_dyadic_width_set_card_le k
  have hc' : (Fintype.card W : ℝ) ≤ k+1 := by exact_mod_cast hc
  have hp : (Fintype.card W : ℝ)^2 ≤ (k+1 : ℝ)^2 := by
    exact pow_le_pow_left₀ (by positivity) hc' 2
  exact h.trans (mul_le_mul_of_nonneg_right hp (mul_nonneg hC hE))

end OpenAI086
