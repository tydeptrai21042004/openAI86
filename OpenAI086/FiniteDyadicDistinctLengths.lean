import Mathlib
import OpenAI086.FiniteDyadicPrefixBlocks

/-!
# Lemma 3.3: each dyadic block length occurs at most once

The existing constructor `finiteDyadicPrefixBlocks` produced an exact
partition with at most k+1 blocks, but its crucial *one block per
length* property had not been recorded as a Lean theorem.  This file
proves it from the recursion, without any analytic assumptions.

Together with the earlier exact scalar/operator prefix identity, this
is the combinatorial input needed to index the paper's variable-prefix
row sums by binary block lengths. It does not by itself establish the
Hilbert Bessel estimate or the general noncommuting product theorem.
-/

namespace OpenAI086

/-- Every block output by the dyadic constructor is no longer than the
prefix being decomposed, including the recursive tail of a split. -/
theorem finite_dyadic_width_le_length (k : ℕ) :
    ∀ start length : ℕ, length ≤ 2 ^ k →
      ∀ b : ℕ × ℕ, b ∈ finiteDyadicPrefixBlocks k start length →
        b.2 ≤ length := by
  induction k with
  | zero =>
      intro start length hlength b hb
      have hbound : length ≤ 1 := by simpa using hlength
      by_cases hz : length = 0
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
      · have h1 : length = 1 := by omega
        subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        norm_num
  | succ k ih =>
      intro start length hlength b hb
      by_cases hf : length = 2 ^ (k + 1)
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        exact le_rfl
      · by_cases hl : length ≤ 2 ^ k
        · have hb' : b ∈ finiteDyadicPrefixBlocks k start length := by
            simpa [finiteDyadicPrefixBlocks, hf, hl] using hb
          exact ih start length hl b hb'
        · have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
            simp [pow_succ, mul_two]
          have hr : length - 2 ^ k ≤ 2 ^ k := by omega
          have hb' : b = (start, 2 ^ k) ∨
              b ∈ finiteDyadicPrefixBlocks k
                (start + 2 ^ k) (length - 2 ^ k) := by
            simpa [finiteDyadicPrefixBlocks, hf, hl] using hb
          rcases hb' with hhead | htail
          · subst b
            dsimp
            omega
          · have hs := ih (start + 2 ^ k) (length - 2 ^ k) hr b htail
            omega

/-- All nonempty blocks have genuinely dyadic (power-of-two) lengths.
This is independent of which prefix is chosen. -/
theorem finite_dyadic_width_is_power_two (k : ℕ) :
    ∀ start length : ℕ, length ≤ 2 ^ k →
      ∀ b : ℕ × ℕ, b ∈ finiteDyadicPrefixBlocks k start length →
        ∃ j : ℕ, j ≤ k ∧ b.2 = 2 ^ j := by
  induction k with
  | zero =>
      intro start length hlength b hb
      have hbound : length ≤ 1 := by simpa using hlength
      by_cases hz : length = 0
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
      · have h1 : length = 1 := by omega
        subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        exact ⟨0, le_rfl, by norm_num⟩
  | succ k ih =>
      intro start length hlength b hb
      by_cases hf : length = 2 ^ (k + 1)
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        exact ⟨k + 1, le_rfl, rfl⟩
      · by_cases hl : length ≤ 2 ^ k
        · have hb' : b ∈ finiteDyadicPrefixBlocks k start length := by
            simpa [finiteDyadicPrefixBlocks, hf, hl] using hb
          obtain ⟨j, hj, hpow⟩ := ih start length hl b hb'
          exact ⟨j, by omega, hpow⟩
        · have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
            simp [pow_succ, mul_two]
          have hr : length - 2 ^ k ≤ 2 ^ k := by omega
          have hb' : b = (start, 2 ^ k) ∨
              b ∈ finiteDyadicPrefixBlocks k
                (start + 2 ^ k) (length - 2 ^ k) := by
            simpa [finiteDyadicPrefixBlocks, hf, hl] using hb
          rcases hb' with hhead | htail
          · subst b
            exact ⟨k, by omega, rfl⟩
          · obtain ⟨j, hj, hpow⟩ :=
              ih (start + 2 ^ k) (length - 2 ^ k) hr b htail
            exact ⟨j, by omega, hpow⟩

/-- Exactly the combinatorial invariant used in the binary-prefix
proof of Lemma 3.3: no two selected blocks have the same width. -/
theorem finite_dyadic_prefix_widths_nodup (k : ℕ) :
    ∀ start length : ℕ, length ≤ 2 ^ k →
      ((finiteDyadicPrefixBlocks k start length).map Prod.snd).Nodup := by
  induction k with
  | zero =>
      intro start length hlength
      have hbound : length ≤ 1 := by simpa using hlength
      by_cases hz : length = 0
      · subst length
        simp [finiteDyadicPrefixBlocks]
      · have h1 : length = 1 := by omega
        subst length
        simp [finiteDyadicPrefixBlocks]
  | succ k ih =>
      intro start length hlength
      by_cases hf : length = 2 ^ (k + 1)
      · simp [finiteDyadicPrefixBlocks, hf]
      · by_cases hl : length ≤ 2 ^ k
        · simpa [finiteDyadicPrefixBlocks, hf, hl] using
            ih start length hl
        · have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
            simp [pow_succ, mul_two]
          have hr : length - 2 ^ k ≤ 2 ^ k := by omega
          have hsmall : length - 2 ^ k < 2 ^ k := by omega
          have htail := ih (start + 2 ^ k) (length - 2 ^ k) hr
          have hnot : 2 ^ k ∉
              (finiteDyadicPrefixBlocks k
                (start + 2 ^ k) (length - 2 ^ k)).map Prod.snd := by
            intro hm
            rcases List.mem_map.mp hm with ⟨b, hb, heq⟩
            have hwidth := finite_dyadic_width_le_length k
              (start + 2 ^ k) (length - 2 ^ k) hr b hb
            omega
          have hcons :
              (2 ^ k :: (finiteDyadicPrefixBlocks k
                (start + 2 ^ k) (length - 2 ^ k)).map Prod.snd).Nodup :=
            List.nodup_cons.mpr ⟨hnot, htail⟩
          simpa [finiteDyadicPrefixBlocks, hf, hl] using hcons


/-- Starting with a dyadically aligned base, every returned block is
aligned to its *own* width. Consequently the blocks of a given width,
taken across different prefix choices, lie in one fixed dyadic grid.
Combined with `finite_dyadic_prefix_widths_nodup`, this is the
combinatorial geometry needed for the fixed-length Bessel argument. -/
theorem finite_dyadic_prefix_block_aligned (k : ℕ) :
    ∀ start length : ℕ, length ≤ 2 ^ k → 2 ^ k ∣ start →
      ∀ b : ℕ × ℕ, b ∈ finiteDyadicPrefixBlocks k start length →
        b.2 ∣ b.1 := by
  induction k with
  | zero =>
      intro start length hlength _ b hb
      have hbound : length ≤ 1 := by simpa using hlength
      by_cases hz : length = 0
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
      · have h1 : length = 1 := by omega
        subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        exact one_dvd _
  | succ k ih =>
      intro start length hlength hstart b hb
      have hpow : 2 ^ k ∣ 2 ^ (k + 1) := by
        refine ⟨2, ?_⟩
        simp [pow_succ, mul_comm]
      have hbase : 2 ^ k ∣ start := dvd_trans hpow hstart
      by_cases hf : length = 2 ^ (k + 1)
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        exact hstart
      · by_cases hl : length ≤ 2 ^ k
        · have hb' : b ∈ finiteDyadicPrefixBlocks k start length := by
            simpa [finiteDyadicPrefixBlocks, hf, hl] using hb
          exact ih start length hl hbase b hb'
        · have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
            simp [pow_succ, mul_two]
          have hr : length - 2 ^ k ≤ 2 ^ k := by omega
          have hb' : b = (start, 2 ^ k) ∨
              b ∈ finiteDyadicPrefixBlocks k
                (start + 2 ^ k) (length - 2 ^ k) := by
            simpa [finiteDyadicPrefixBlocks, hf, hl] using hb
          rcases hb' with hhead | htail
          · subst b
            exact hbase
          · exact ih (start + 2 ^ k) (length - 2 ^ k)
              hr (dvd_add hbase (dvd_refl _)) b htail

/-- Different grid cells of the same strictly positive width never
overlap in their interiors. This is an arithmetic implication of their
common dyadic alignment, independent of the projection operators. -/
theorem aligned_equal_width_intervals_separated
    (startA startB width : ℕ)
    (hpos : 0 < width) (ha : width ∣ startA)
    (hb : width ∣ startB) (hne : startA ≠ startB) :
    startA + width ≤ startB ∨ startB + width ≤ startA := by
  obtain ⟨a, ha'⟩ := ha
  obtain ⟨b, hb'⟩ := hb
  have hab : a ≠ b := by
    intro heq
    apply hne
    simpa [ha', hb', heq]
  by_cases hlt : a < b
  · left
    have hle : a + 1 ≤ b := by omega
    have hmul := Nat.mul_le_mul_left width hle
    calc
      startA + width = width * (a + 1) := by rw [ha']; ring
      _ ≤ width * b := hmul
      _ = startB := by exact hb'.symm
  · right
    have hlt' : b < a := by omega
    have hle : b + 1 ≤ a := by omega
    have hmul := Nat.mul_le_mul_left width hle
    calc
      startB + width = width * (b + 1) := by rw [hb']; ring
      _ ≤ width * a := hmul
      _ = startA := by exact ha'.symm

end OpenAI086
