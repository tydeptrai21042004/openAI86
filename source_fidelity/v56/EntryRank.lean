/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0; see LICENSE-REFERENCE-APACHE2 at the project root.
Adapted from lean-trilinearht, commit 7b4209609e6a7fb9d9935973ee8541495f943660,
TrilinearHT/Auto/Sec13_3BesselRowsLinearSideEnergy.lean, lines 206–350.
Original file attributes generation to Claude. V56 changes: isolated Mathlib
import, names and namespace; added the exact H_M statement below.
This file is not part of the independently derived OpenAI086 import tree.
-/
import Mathlib

noncomputable section
namespace OpenAI086.AdaptedV56
open scoped BigOperators

/-- `(b - a)/b ≤ H_b - H_a` for harmonic numbers. -/
theorem v56_frac_le_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    ((b - a : ℕ) : ℝ) / b ≤ (harmonic b : ℝ) - harmonic a := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; obtain rfl : a = 0 := by omega
    simp
  have he : (harmonic b : ℝ) - harmonic a = ∑ i ∈ Finset.Ico a b, ((i + 1 : ℕ) : ℝ)⁻¹ := by
    rw [Finset.sum_Ico_eq_sub _ hab]
    simp [harmonic]
  rw [he]
  calc ((b - a : ℕ) : ℝ) / b = ∑ _i ∈ Finset.Ico a b, (b : ℝ)⁻¹ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ ∑ i ∈ Finset.Ico a b, ((i + 1 : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum; intro i hi
        have := (Finset.mem_Ico.mp hi).2
        apply inv_anti₀ (by positivity)
        exact_mod_cast (show i + 1 ≤ b by omega)

/-- Blueprint lines 2093-2094 (elementary fact): if nonempty sets `S_j` increase from `S_0 = ∅`,
`X_j ⊆ S_j`, and each label belongs to at most `A` of the `X_j`, then
`Σ_j |X_j|/|S_j| ≤ A H_{|S_n|}`; enumerate labels by first entry. -/
theorem v56_sum_frac_le_harmonic {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (hS : Monotone S)
    (hS0 : S 0 = ∅) (X : ℕ → Finset α) (hX : ∀ j, X j ⊆ S j) (n A : ℕ)
    (hA : ∀ x, ((Finset.range n).filter fun j => x ∈ X (j + 1)).card ≤ A) :
    ∑ j ∈ Finset.range n, ((X (j + 1)).card : ℝ) / (S (j + 1)).card ≤
      A * (harmonic (S n).card : ℝ) := by
  classical
  -- first entry
  let f : α → ℕ := fun x => if h : ∃ j, x ∈ S j then Nat.find h else 0
  have hf_mem : ∀ x j, x ∈ S j → x ∈ S (f x) ∧ f x ≤ j := by
    intro x j hx
    have h : ∃ j, x ∈ S j := ⟨j, hx⟩
    simp only [f, h, ↓reduceDIte]
    exact ⟨Nat.find_spec h, Nat.find_min' h hx⟩
  have hf_pos : ∀ x j, x ∈ S j → 1 ≤ f x := by
    intro x j hx
    by_contra h0
    have := (hf_mem x j hx).1
    rw [show f x = 0 by omega, hS0] at this
    simp at this
  have hf_not : ∀ x j, x ∈ S j → x ∉ S (f x - 1) := by
    intro x j hx hmem
    have h : ∃ j, x ∈ S j := ⟨j, hx⟩
    have hle := hf_mem x (f x - 1) hmem
    have := hf_pos x j hx
    omega
  -- step 1: replace `|S_{j+1}|` by `|S_{f x}|`
  have step1 : ∑ j ∈ Finset.range n, ((X (j + 1)).card : ℝ) / (S (j + 1)).card ≤
      ∑ j ∈ Finset.range n, ∑ x ∈ X (j + 1), ((S (f x)).card : ℝ)⁻¹ := by
    apply Finset.sum_le_sum; intro j _
    rw [div_eq_mul_inv, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum; intro x hx
    have hxS := hX _ hx
    obtain ⟨hxf, hfj⟩ := hf_mem x _ hxS
    have hpos : (0 : ℝ) < (S (f x)).card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hxf⟩
    apply inv_anti₀ hpos
    exact_mod_cast Finset.card_le_card (hS hfj)
  -- step 2: exchange the sums
  have step2 : ∑ j ∈ Finset.range n, ∑ x ∈ X (j + 1), ((S (f x)).card : ℝ)⁻¹ ≤
      A * ∑ x ∈ S n, ((S (f x)).card : ℝ)⁻¹ := by
    have hre : ∀ j ∈ Finset.range n, ∑ x ∈ X (j + 1), ((S (f x)).card : ℝ)⁻¹ =
        ∑ x ∈ S n, if x ∈ X (j + 1) then ((S (f x)).card : ℝ)⁻¹ else 0 := by
      intro j hj
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨hS (by have := Finset.mem_range.mp hj; omega) (hX _ hx), hx⟩
      · exact fun h => h.2
    rw [Finset.sum_congr rfl hre, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum; intro x _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA x) (by positivity)
  -- step 3: group labels by first entry
  have step3 : ∑ x ∈ S n, ((S (f x)).card : ℝ)⁻¹ =
      ∑ i ∈ Finset.range n, ((S (i + 1) \ S i).card : ℝ) / (S (i + 1)).card := by
    have hmaps : ∀ x ∈ S n, f x - 1 ∈ Finset.range n := by
      intro x hx
      have := hf_mem x n hx
      have := hf_pos x n hx
      rw [Finset.mem_range]; omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl; intro i hi
    have hfib : (S n).filter (fun x => f x - 1 = i) = S (i + 1) \ S i := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hx, hfx⟩
        have h1 := hf_mem x n hx
        have h2 := hf_pos x n hx
        have h3 := hf_not x n hx
        refine ⟨?_, ?_⟩
        · rw [show i + 1 = f x by omega]; exact h1.1
        · rw [show i = f x - 1 by omega]; exact h3
      · rintro ⟨hx1, hx0⟩
        refine ⟨hS (by have := Finset.mem_range.mp hi; omega) hx1, ?_⟩
        have h1 := hf_mem x (i + 1) hx1
        have h2 := hf_pos x (i + 1) hx1
        by_contra hne
        have hlt : f x ≤ i := by omega
        exact hx0 (hS hlt h1.1)
    have hconst : ∀ x ∈ (S n).filter (fun x => f x - 1 = i),
        ((S (f x)).card : ℝ)⁻¹ = ((S (i + 1)).card : ℝ)⁻¹ := by
      intro x hx
      obtain ⟨hxn, hfx⟩ := Finset.mem_filter.mp hx
      have := hf_pos x n hxn
      rw [show f x = i + 1 by omega]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hfib, div_eq_mul_inv]
  -- step 4: telescoping harmonic numbers
  have step4 : ∑ i ∈ Finset.range n, ((S (i + 1) \ S i).card : ℝ) / (S (i + 1)).card ≤
      harmonic (S n).card := by
    calc _ ≤ ∑ i ∈ Finset.range n,
          ((harmonic (S (i + 1)).card : ℝ) - harmonic (S i).card) := by
          apply Finset.sum_le_sum; intro i _
          rw [Finset.card_sdiff_of_subset (hS (Nat.le_succ i))]
          exact v56_frac_le_harmonic_sub (Finset.card_le_card (hS (Nat.le_succ i)))
      _ = harmonic (S n).card := by
          rw [Finset.sum_range_sub (fun i => (harmonic (S i).card : ℝ)), hS0]
          simp
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ A * (harmonic (S n).card : ℝ) := by
        rw [step3]
        exact mul_le_mul_of_nonneg_left step4 (by positivity)

/-- Corollary: `Σ_j |X_j|/|S_j| ≤ A (1 + log M)` when `|S_n| ≤ M`. -/
theorem v56_sum_frac_le_log {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (hS : Monotone S)
    (hS0 : S 0 = ∅) (X : ℕ → Finset α) (hX : ∀ j, X j ⊆ S j) (n A M : ℕ)
    (hA : ∀ x, ((Finset.range n).filter fun j => x ∈ X (j + 1)).card ≤ A)
    (hM : (S n).card ≤ M) :
    ∑ j ∈ Finset.range n, ((X (j + 1)).card : ℝ) / (S (j + 1)).card ≤ A * (1 + Real.log M) := by
  refine (v56_sum_frac_le_harmonic S hS hS0 X hX n A hA).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (harmonic_le_one_add_log _).trans ?_
  rcases Nat.eq_zero_or_pos (S n).card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero, add_zero]
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · simp [hM0]
    · have : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
      linarith only [Real.log_nonneg this]
  · gcongr

/-- Lemma 8.5 with both of its bounds. The source sets S_1,...,S_T
are represented by S(1),...,S(T), with an empty S(0) prepended. For a
noninteger M or A take their natural floors; the counting hypotheses
are integral. No ranks or rank-size hypotheses are assumed. -/
theorem v56_lemma85 {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (hS : Monotone S) (hS0 : S 0 = ∅)
    (X : ℕ → Finset α) (hX : ∀ j, X j ⊆ S j) (T A M : ℕ)
    (hA : ∀ x, ((Finset.range T).filter fun j => x ∈ X (j+1)).card ≤ A)
    (hM : (S T).card ≤ M) :
    (∑ j ∈ Finset.range T, ((X (j+1)).card : ℝ) / (S (j+1)).card) ≤
      A * (harmonic M : ℝ) ∧ (harmonic M : ℝ) ≤ 1 + Real.log M := by
  have hdiff := v56_frac_le_harmonic_sub hM
  have hnon : (0:ℝ) ≤ ((M - (S T).card : ℕ) : ℝ) / (M:ℝ) := by positivity
  have hh : (harmonic (S T).card : ℝ) ≤ (harmonic M : ℝ) := by linarith
  exact ⟨(v56_sum_frac_le_harmonic S hS hS0 X hX T A hA).trans
    (mul_le_mul_of_nonneg_left hh (by positivity)), harmonic_le_one_add_log M⟩

end OpenAI086.AdaptedV56

#print axioms OpenAI086.AdaptedV56.v56_lemma85
