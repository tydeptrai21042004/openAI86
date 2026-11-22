import Mathlib
import OpenAI086.PrefixCombinatorics

/-!
# Constructive binary-prefix decomposition (Lemma 3.3)

Every prefix of a range of length `2^k` is represented here by a list
of pairwise consecutive blocks. At each size level at most one block
is selected, so there are at most `k+1` blocks, independently of the
prefix length. We prove that summing any scalar sequence over the
returned blocks gives exactly the original prefix sum.

This is a genuine constructive combinatorial sublemma, separate from
the Bessel estimates for noncommuting projection products. The next
integration step is to turn every returned block into an aligned
projection increment at the appropriate length and match the paper's
index convention (including its initial `P₀` term).
-/

namespace OpenAI086

/-- Blocks are encoded by `(start, length)`; the last endpoint is
`start + length`. The algorithm makes at most one recursive call
at each depth and needs no search or backtracking. -/
def finiteDyadicPrefixBlocks : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, start, length =>
      if length = 0 then [] else [(start, 1)]
  | k + 1, start, length =>
      if length = 2 ^ (k + 1) then
        [(start, 2 ^ (k + 1))]
      else if length ≤ 2 ^ k then
        finiteDyadicPrefixBlocks k start length
      else
        (start, 2 ^ k) ::
          finiteDyadicPrefixBlocks k (start + 2 ^ k) (length - 2 ^ k)

/-- Finite sum along the returned ordered intervals. -/
def finiteDyadicBlockSum (f : ℕ → ℝ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | (start, width) :: rest =>
      (∑ j ∈ Finset.range width, f (start + j)) +
        finiteDyadicBlockSum f rest

/-- Exactly reproduces the original prefix, without periodicity,
orthogonality or any assumptions on the scalar sequence. -/
theorem finite_dyadic_prefix_sum_exact
    (f : ℕ → ℝ) (k : ℕ) :
    ∀ (start length : ℕ), length ≤ 2 ^ k →
      finiteDyadicBlockSum f (finiteDyadicPrefixBlocks k start length) =
        ∑ j ∈ Finset.range length, f (start + j) := by
  induction k with
  | zero =>
      intro start length hlength
      have hbound : length ≤ 1 := by simpa using hlength
      have hsmall : length = 0 ∨ length = 1 := by omega
      rcases hsmall with hzero | hone
      · subst length
        simp [finiteDyadicPrefixBlocks, finiteDyadicBlockSum]
      · subst length
        simp [finiteDyadicPrefixBlocks, finiteDyadicBlockSum]
  | succ k ih =>
      intro start length hlength
      by_cases hfull : length = 2 ^ (k + 1)
      · simp [finiteDyadicPrefixBlocks, hfull, finiteDyadicBlockSum]
      · by_cases hleft : length ≤ 2 ^ k
        · simpa [finiteDyadicPrefixBlocks, hfull, hleft] using
            ih start length hleft
        · have hright : length - 2 ^ k ≤ 2 ^ k := by
            have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
              simp [pow_succ, mul_two]
            omega
          have hsum : 2 ^ k + (length - 2 ^ k) = length := by
            omega
          have htail := ih (start + 2 ^ k) (length - 2 ^ k) hright
          have hsplit := finite_prefix_concat
            (fun j : ℕ => f (start + j)) (2 ^ k) (length - 2 ^ k)
          rw [hsum] at hsplit
          simp only [finiteDyadicPrefixBlocks, if_neg hfull,
            if_neg hleft, finiteDyadicBlockSum]
          rw [htail]
          rw [hsplit]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          simp only [Nat.add_assoc]

/-- Constructive logarithmic block-count bound. Under the input
`length ≤ 2^k` there are at most `k+1` output blocks. -/
theorem finite_dyadic_prefix_length_le
    (k : ℕ) : ∀ (start length : ℕ), length ≤ 2 ^ k →
      (finiteDyadicPrefixBlocks k start length).length ≤ k + 1 := by
  induction k with
  | zero =>
      intro start length _
      simp only [finiteDyadicPrefixBlocks]
      split_ifs <;> simp
  | succ k ih =>
      intro start length hlength
      by_cases hfull : length = 2 ^ (k + 1)
      · simp [finiteDyadicPrefixBlocks, hfull]
      · by_cases hleft : length ≤ 2 ^ k
        · have h := ih start length hleft
          simp only [finiteDyadicPrefixBlocks, if_neg hfull, if_pos hleft]
          omega
        · have hright : length - 2 ^ k ≤ 2 ^ k := by
            have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
              simp [pow_succ, mul_two]
            omega
          have h := ih (start + 2 ^ k) (length - 2 ^ k) hright
          simp only [finiteDyadicPrefixBlocks, if_neg hfull,
            if_neg hleft, List.length_cons]
          omega

end OpenAI086
