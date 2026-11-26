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


/-! V57: the manuscript's floor-log bad-density chain, rather than the
reference's continuous 90%-density test. Terminal P⊆C is explicit.
The entry-rank result above is reused with the harmonic constant itself. -/
namespace OpenAI086.AdaptedV56
open scoped BigOperators

/-- A bounded nondecreasing sequence has at most Δ L total backward-lag
variation. The proof counts the first Δ heights separately via the
clamped index. -/
theorem v57_backward_lag (p : ℕ → ℝ) (L : ℝ) (Δ H : ℕ)
    (hp : Monotone p) (h0 : ∀ h, 0 ≤ p h) (hL : ∀ h, p h ≤ L) :
    (∑ h ∈ Finset.range H, (p h - p (h-Δ))) ≤ Δ * L := by
  have htel : ∀ n : ℕ,
      (∑ h ∈ Finset.range (n+Δ), (p h - p (h-Δ))) =
        ∑ j ∈ Finset.range Δ, (p (n+j)-p 0) := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.sub_eq_zero_of_le (Finset.mem_range.mp hj).le]
    | succ n ih =>
      rw [show n+1+Δ = n+Δ+1 by omega, Finset.sum_range_succ, ih,
        show n+Δ-Δ=n by omega]
      have hshift := Finset.sum_range_sub (fun j => p (n+j)) Δ
      simp only [add_zero] at hshift
      calc
        _ = (∑ j ∈ Finset.range Δ, (p (n+j)-p 0)) +
              ∑ j ∈ Finset.range Δ, (p (n+(j+1))-p (n+j)) := by rw [hshift]
        _ = _ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [show n+1+j=n+(j+1) by omega]
          ring
  have hsub : Finset.range H ⊆ Finset.range (H+Δ) := Finset.range_mono (by omega)
  calc
    _ ≤ ∑ h ∈ Finset.range (H+Δ), (p h-p (h-Δ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => sub_nonneg.mpr (hp (Nat.sub_le h Δ)))
    _ = ∑ j ∈ Finset.range Δ, (p (H+j)-p 0) := htel H
    _ ≤ ∑ _j ∈ Finset.range Δ, L := Finset.sum_le_sum fun j _ => by linarith [h0 0,hL (H+j)]
    _ = _ := by simp

/-- Include the last position in the temporal chain, without imposing
any ordering on a fictitious position after it. -/
theorem v57_interleaved (p c : ℕ → ℝ) (N : ℕ)
    (h : ∀ i < N, c i ≤ p (i+1)) :
    (∑ i ∈ Finset.range (N+1), (c i-p i)) ≤ c N-p 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hb := ih (fun i hi => h i (by omega))
    linarith [h n (by omega)]

/-- The entry-rank harmonic estimate with zero-based input stages and
no artificial initial empty-set requirement on those input stages. -/
theorem v57_fraction_budget {α : Type*} [DecidableEq α]
    (S X : ℕ → Finset α) (hS : Monotone S) (hX : ∀ j, X j ⊆ S j)
    (n A M : ℕ) (hM : ∀ j, (S j).card ≤ M)
    (hA : ∀ x, ((Finset.range n).filter fun j => x ∈ X j).card ≤ A) :
    (∑ j ∈ Finset.range n, ((X j).card : ℝ)/(S j).card) ≤ A*(harmonic M : ℝ) := by
  let S' : ℕ → Finset α := fun j => if j=0 then ∅ else S (j-1)
  let X' : ℕ → Finset α := fun j => if j=0 then ∅ else X (j-1)
  have hm : Monotone S' := by
    apply monotone_nat_of_le_succ
    intro j
    by_cases hj : j=0
    · subst j; simp [S']
    · simp only [S', hj, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact hS (Nat.sub_le j 1)
  have hsub : ∀ j, X' j ⊆ S' j := by
    intro j; by_cases hj : j=0 <;> simp [X', S', hj, hX]
  have hinc : ∀ x, ((Finset.range n).filter fun j => x ∈ X' (j+1)).card ≤ A := by
    intro x; simpa [X'] using hA x
  have hc : (S' n).card ≤ M := by
    by_cases hn : n=0 <;> simp [S', hn, hM]
  simpa [X', S'] using (v56_lemma85 S' hm (by simp [S']) X' hsub n A M hinc hc).1

/-- The bad indicator uses the *integer floor-log rank* of the paper.
The generic monotone rank makes the counting proof independent of how
logarithms are computed. -/
def v57Bad {α : Type*} [DecidableEq α] (rank : ℕ → ℕ)
    (P C : ℕ → ℕ → Finset α) (X : ℕ → Finset α) (Y : ℕ → ℕ → Finset α)
    (Δ : ℕ) (β : ℝ) (i h : ℕ) : Prop :=
  h < Δ ∨ rank (P i (h-Δ)).card ≠ rank (C i h).card ∨
    β < (((X i ∪ Y i h) ∩ C i h).card : ℝ)/(C i h).card

/-- Lemma 8.6 with the explicit terminal inclusion (and the exact
harmonic coefficient). N+1 positions, J+1 heights; sets may be extended
constantly past the finite range. The bad-count assumptions are those
of the paper, not pre-assumed total fractional-incidence bounds. -/
open Classical in
theorem v57_lemma86_rank {α : Type*} [DecidableEq α]
    (N J Δ M A B : ℕ) (δ β : ℝ) (rank : ℕ → ℕ) (hr : Monotone rank)
    (P C : ℕ → ℕ → Finset α) (X : ℕ → Finset α) (Y : ℕ → ℕ → Finset α)
    (hδ : 0 < δ) (hβ : 0 < β) (hP : ∀ i h, (P i h).Nonempty)
    (hPC : ∀ i h, P i h ⊆ C i h) (hCP : ∀ i < N, ∀ h, C i h ⊆ P (i+1) h)
    (hPm : ∀ i, Monotone (P i)) (hCm : ∀ i, Monotone (C i))
    (hM : ∀ i h, (C i h).card ≤ M)
    (hA : ∀ i x, ((Finset.range (J+1)).filter fun h => x ∈ Y i h).card ≤ A)
    (hB : ∀ x, ((Finset.range (N+1)).filter fun i => x ∈ X i).card ≤ B)
    (hbad : ∀ i ≤ N, δ*(J+1 : ℕ) <
      ∑ h ∈ Finset.range (J+1), if v57Bad rank P C X Y Δ β i h then (1:ℝ) else 0)
    (hbudget : 2*((Δ:ℝ)*(rank M+1) + (A:ℝ)*(harmonic M:ℝ)/β) ≤ δ*(J+1 : ℕ)) :
    ((N+1 : ℕ):ℝ) < 2*((rank M:ℝ) + (B:ℝ)*(harmonic M:ℝ)/β)/δ := by
  classical
  let p : ℕ → ℕ → ℝ := fun i h => rank (P i h).card
  let c : ℕ → ℕ → ℝ := fun i h => rank (C i h).card
  let L : ℝ := rank M
  let f : ℕ → ℕ → ℝ := fun i h => (((Y i h ∩ C i h).card : ℝ)/(C i h).card)/β
  let g : ℕ → ℕ → ℝ := fun i h => (((X i ∩ C i h).card : ℝ)/(C i h).card)/β
  let e : ℕ → ℝ := fun h => if h<Δ then 1 else 0
  let bad : ℕ → ℕ → ℝ := fun i h => if v57Bad rank P C X Y Δ β i h then 1 else 0
  have hpc : ∀ i h, p i h ≤ c i h := fun i h => by
    exact_mod_cast hr (Finset.card_le_card (hPC i h))
  have hcp : ∀ i < N, ∀ h, c i h ≤ p (i+1) h := fun i hi h => by
    exact_mod_cast hr (Finset.card_le_card (hCP i hi h))
  have hpmono : ∀ i, Monotone (p i) := fun i a b hab => by
    exact_mod_cast hr (Finset.card_le_card (hPm i hab))
  have hcL : ∀ i h, c i h ≤ L := fun i h => by exact_mod_cast hr (hM i h)
  have hf : ∀ i, ∑ h ∈ Finset.range (J+1), f i h ≤ (A:ℝ)*(harmonic M:ℝ)/β := by
    intro i
    simp only [f, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hβ.le
    apply v57_fraction_budget (C i) (fun h => Y i h ∩ C i h) (hCm i)
      (fun h => Finset.inter_subset_right) (J+1) A M (hM i)
    intro x
    exact (Finset.card_le_card (fun j hj => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_inter.mp (Finset.mem_filter.mp hj).2).1⟩)).trans (hA i x)
  -- The chain is extended constantly beyond its last position before
  -- applying the harmonic lemma: no extra C_N⊆P_{N+1} is assumed.
  have hg : ∀ h, ∑ i ∈ Finset.range (N+1), g i h ≤ (B:ℝ)*(harmonic M:ℝ)/β := by
    intro h
    let S : ℕ → Finset α := fun i => C (min i N) h
    have hS : Monotone S := by
      apply monotone_nat_of_le_succ
      intro i
      by_cases hi : i < N
      · simpa [S, min_eq_left hi.le, min_eq_left (show i+1≤N by omega)] using
          (hCP i hi h).trans (hPC (i+1) h)
      · have hi' : N ≤ i := by omega
        simp [S,min_eq_right hi',min_eq_right (show N≤i+1 by omega)]
    have hcount := v57_fraction_budget S (fun i => X i ∩ S i) hS
      (fun _ => Finset.inter_subset_right) (N+1) B M (fun i => hM (min i N) h) (by
        intro x
        exact (Finset.card_le_card (fun i hi => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_inter.mp (Finset.mem_filter.mp hi).2).1⟩)).trans (hB x))
    simp only [g, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hβ.le
    refine le_trans (le_of_eq ?_) hcount
    apply Finset.sum_congr rfl
    intro i hi
    simp [S,min_eq_left (show i≤N by have := Finset.mem_range.mp hi; omega)]
  have he : ∑ h ∈ Finset.range (J+1), e h ≤ Δ := by
    simp only [e]
    rw [← Finset.sum_filter, Finset.sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast (Finset.card_le_card (show (Finset.range (J+1)).filter (·<Δ) ⊆ Finset.range Δ from
      fun h hh => Finset.mem_range.mpr (Finset.mem_filter.mp hh).2)).trans (Finset.card_range Δ).le
  have hpoint : ∀ i h, bad i h ≤ e h + (p i h-p i (h-Δ)) + (c i h-p i h) + f i h+g i h := by
    intro i h
    have hp0 := sub_nonneg.mpr (hpmono i (Nat.sub_le h Δ))
    have hc0 := sub_nonneg.mpr (hpc i h)
    have hf0 : 0 ≤ f i h := by dsimp [f]; positivity
    have hg0 : 0 ≤ g i h := by dsimp [g]; positivity
    have he0 : 0 ≤ e h := by dsimp [e]; split_ifs <;> norm_num
    by_cases hb : v57Bad rank P C X Y Δ β i h
    · have hb1 : bad i h = 1 := by simp [bad,hb]
      rw [hb1]
      rcases hb with hh | hrank | hfrac
      · have : e h=1 := by simp [e,hh]
        linarith
      · have hrank' : rank (P i (h-Δ)).card < rank (C i h).card :=
          lt_of_le_of_ne (hr (Finset.card_le_card ((hPm i (Nat.sub_le h Δ)).trans (hPC i h)))) hrank
        have : 1 ≤ c i h-p i (h-Δ) := by
          have h := Nat.succ_le_of_lt hrank'
          dsimp [c,p]
          have hc : ((rank (P i (h-Δ)).card:ℕ):ℝ)+1 ≤ (rank (C i h).card:ℝ) := by exact_mod_cast h
          linarith
        linarith
      · have hne : 0 < ((C i h).card:ℝ) := by exact_mod_cast ((hP i h).mono (hPC i h)).card_pos
        have hs : (((X i ∪ Y i h) ∩ C i h).card:ℝ) ≤
            ((X i ∩ C i h).card:ℝ) + ((Y i h ∩ C i h).card:ℝ) := by
          have heq : (X i ∪ Y i h) ∩ C i h = (X i ∩ C i h) ∪ (Y i h ∩ C i h) := by
            ext x; simp only [Finset.mem_inter, Finset.mem_union]; tauto
          rw [heq]
          exact_mod_cast Finset.card_union_le (X i ∩ C i h) (Y i h ∩ C i h)
        have hfrac' := hfrac.trans_le (div_le_div_of_nonneg_right hs hne.le)
        rw [add_div] at hfrac'
        have hfg : 1 < f i h+g i h := by
          dsimp [f,g]
          rw [← add_div, lt_div_iff₀ hβ,one_mul]
          linarith
        linarith
    · have : bad i h = 0 := by simp [bad,hb]
      linarith
  let Q : ℝ := (Δ:ℝ)*(L+1)+(A:ℝ)*(harmonic M:ℝ)/β
  let R : ℝ := L+(B:ℝ)*(harmonic M:ℝ)/β
  have hrow : ∀ i, ∑ h ∈ Finset.range (J+1), (e h+(p i h-p i (h-Δ))+f i h) ≤ Q := by
    intro i
    have hp := v57_backward_lag (p i) L Δ (J+1) (hpmono i)
      (fun h => by dsimp [p]; positivity) (fun h => (hpc i h).trans (hcL i h))
    simp only [Finset.sum_add_distrib]
    dsimp [Q]; linarith [hf i]
  have hcol : ∀ h, ∑ i ∈ Finset.range (N+1), (c i h-p i h+g i h) ≤ R := by
    intro h
    have ht := v57_interleaved (fun i => p i h) (fun i => c i h) N (fun i hi => hcp i hi h)
    have h0 : 0≤p 0 h := by dsimp [p]; positivity
    simp only [Finset.sum_add_distrib]
    dsimp [R]; linarith [hg h,hcL N h]
  have hupper : ∑ i ∈ Finset.range (N+1), ∑ h ∈ Finset.range (J+1), bad i h ≤
      (N+1:ℕ)*Q+(J+1:ℕ)*R := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N+1), ∑ h ∈ Finset.range (J+1),
          ((e h+(p i h-p i (h-Δ))+f i h)+(c i h-p i h+g i h)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun h _ => by linarith [hpoint i h]
      _ = (∑ i ∈ Finset.range (N+1), ∑ h ∈ Finset.range (J+1), (e h+(p i h-p i (h-Δ))+f i h)) +
          (∑ h ∈ Finset.range (J+1), ∑ i ∈ Finset.range (N+1), (c i h-p i h+g i h)) := by
        rw [Finset.sum_comm (s:=Finset.range (J+1)) (t:=Finset.range (N+1))
          (f:=fun h i => c i h-p i h+g i h)]
        simp only [Finset.sum_add_distrib]
        <;> ring
      _ ≤ _ := add_le_add ((Finset.sum_le_sum fun i _ => hrow i).trans (by simp))
        ((Finset.sum_le_sum fun h _ => hcol h).trans (by simp))
  have hlower : (N+1:ℕ)*(δ*(J+1:ℕ)) < ∑ i ∈ Finset.range (N+1), ∑ h ∈ Finset.range (J+1), bad i h := by
    have hs : (∑ _i ∈ Finset.range (N+1), δ*(J+1:ℕ)) <
        ∑ i ∈ Finset.range (N+1), ∑ h ∈ Finset.range (J+1), bad i h := by
      apply Finset.sum_lt_sum
      · intro i hi; exact (hbad i (by have := Finset.mem_range.mp hi; omega)).le
      · exact ⟨0, by simp, hbad 0 (Nat.zero_le N)⟩
    simpa using hs
  have hb : 2*Q ≤ δ*(J+1:ℕ) := hbudget
  have hm := mul_le_mul_of_nonneg_left hb (show 0≤((N+1:ℕ):ℝ) by positivity)
  have ht : ((N+1:ℕ):ℝ)*δ*((J+1:ℕ):ℝ) < (2*R)*((J+1:ℕ):ℝ) := by nlinarith
  have hres := (mul_lt_mul_right (show 0 < ((J+1:ℕ):ℝ) by positivity)).mp ht
  exact (lt_div_iff₀ hδ).mpr hres

/-- Natural floor of log base 1.1. On nonempty finite sets this is the
ordinary nonnegative floor of the logarithm. -/
noncomputable def v57FloorLog (n : ℕ) : ℕ := ⌊Real.log (n:ℝ) / Real.log (11/10:ℝ)⌋₊

theorem v57_floorLog_mono : Monotone v57FloorLog := by
  intro a b hab
  by_cases ha : a=0
  · simp [v57FloorLog,ha]
  · apply Nat.floor_mono
    exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha)
      (by exact_mod_cast hab)) (Real.log_nonneg (by norm_num))

/-- The corrected printed floor-log assertion, with exact H_M, strict
bad-density test and terminal inclusion. -/
open Classical in
theorem v57_lemma86 {α : Type*} [DecidableEq α]
    (N J Δ M A B : ℕ) (δ β : ℝ)
    (P C : ℕ → ℕ → Finset α) (X : ℕ → Finset α) (Y : ℕ → ℕ → Finset α)
    (hδ : 0 < δ) (hβ : 0 < β) (hP : ∀ i h, (P i h).Nonempty)
    (hPC : ∀ i h, P i h ⊆ C i h) (hCP : ∀ i < N, ∀ h, C i h ⊆ P (i+1) h)
    (hPm : ∀ i, Monotone (P i)) (hCm : ∀ i, Monotone (C i))
    (hM : ∀ i h, (C i h).card ≤ M)
    (hA : ∀ i x, ((Finset.range (J+1)).filter fun h => x ∈ Y i h).card ≤ A)
    (hB : ∀ x, ((Finset.range (N+1)).filter fun i => x ∈ X i).card ≤ B)
    (hbad : ∀ i ≤ N, δ*(J+1 : ℕ) <
      ∑ h ∈ Finset.range (J+1), if v57Bad v57FloorLog P C X Y Δ β i h then (1:ℝ) else 0)
    (hbudget : 2*((Δ:ℝ)*(v57FloorLog M+1) + (A:ℝ)*(harmonic M:ℝ)/β) ≤ δ*(J+1 : ℕ)) :
    ((N+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ) + (B:ℝ)*(harmonic M:ℝ)/β)/δ :=
  v57_lemma86_rank N J Δ M A B δ β v57FloorLog v57_floorLog_mono
    P C X Y hδ hβ hP hPC hCP hPm hCm hM hA hB hbad hbudget

end OpenAI086.AdaptedV56

#print axioms OpenAI086.AdaptedV56.v57_lemma86
#print axioms OpenAI086.AdaptedV56.v57_lemma86_rank
#print axioms OpenAI086.AdaptedV56.v57_floorLog_mono
