import Mathlib
import OpenAI086.FiniteDyadicDistinctLengths

/-!
# V17: bounded aligned block indices for binary prefixes

The V16 row selector returned `Nat` block numbers. The fixed-tuple
Bessel theorem, however, uses indices of type `Fin count`. This file
proves the missing FINITENESS statement from the real prefix algorithm:
for prefixes of length at most `2^k` starting at zero, every selected
aligned block has a block index strictly below `2^k`.

No projection estimate is asserted here. This is a purely combinatorial
fact and does not assume a bound on the selected block number.
-/

namespace OpenAI086

/-- Every returned dyadic block is inside the input prefix, including
its right endpoint. This also gives a useful check that the recursive
tail does not extend past the requested interval. -/
theorem finite_dyadic_prefix_block_inside (k : ℕ) :
    ∀ (start length : ℕ), length ≤ 2 ^ k →
      ∀ b : ℕ × ℕ, b ∈ finiteDyadicPrefixBlocks k start length →
        start ≤ b.1 ∧ b.1 + b.2 ≤ start + length := by
  induction k with
  | zero =>
      intro start length hlength b hb
      have hsmall : length = 0 ∨ length = 1 := by
        have hp : 2 ^ (0 : ℕ) = 1 := by norm_num
        omega
      rcases hsmall with hz | ho
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        constructor <;> simp
  | succ k ih =>
      intro start length hlength b hb
      by_cases hf : length = 2 ^ (k + 1)
      · subst length
        simp [finiteDyadicPrefixBlocks] at hb
        rcases hb with rfl
        constructor <;> simp
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
            constructor <;> dsimp <;> omega
          · obtain ⟨hlo, hhi⟩ :=
              ih (start + 2 ^ k) (length - 2 ^ k) hr b htail
            constructor <;> omega

/-- For a nonempty dyadic block in a zero-based prefix, its starting
position is strictly below the common budget `2^k`. -/
theorem finite_dyadic_zero_base_start_lt (k length : ℕ)
    (hlen : length ≤ 2 ^ k) (b : ℕ × ℕ)
    (hb : b ∈ finiteDyadicPrefixBlocks k 0 length) :
    b.1 < 2 ^ k := by
  obtain ⟨_, hend⟩ :=
    finite_dyadic_prefix_block_inside k 0 length hlen b hb
  obtain ⟨j, _, hwidth⟩ :=
    finite_dyadic_width_is_power_two k 0 length hlen b hb
  have hpositive : 0 < b.2 := by
    rw [hwidth]
    positivity
  omega

/-- The aligned integer-grid block index is uniformly bounded by the
same power of two, independent of the row and of the block width. -/
theorem finite_dyadic_aligned_block_index_lt (k length : ℕ)
    (hlen : length ≤ 2 ^ k) (b : ℕ × ℕ)
    (hb : b ∈ finiteDyadicPrefixBlocks k 0 length)
    (index : ℕ) (hindex : b.1 = index * b.2) :
    index < 2 ^ k := by
  have hstart := finite_dyadic_zero_base_start_lt k length hlen b hb
  obtain ⟨j, _, hwidth⟩ :=
    finite_dyadic_width_is_power_two k 0 length hlen b hb
  have hone : 1 ≤ b.2 := by
    rw [hwidth]
    positivity
  have hle : index ≤ index * b.2 := by
    calc
      index = index * 1 := by omega
      _ ≤ index * b.2 := Nat.mul_le_mul_left index hone
  omega

end OpenAI086
