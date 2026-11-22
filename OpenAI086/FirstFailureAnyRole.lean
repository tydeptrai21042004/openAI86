import Mathlib

/-!
# First-failing-role decomposition at arbitrary finite arity (§9.1)

In the first-success sampling argument the first failed role has all
PRECEDING roles successful; later roles are unrestricted. This module
makes that convention exact for an arbitrary list of Boolean tests,
not only for the fixed three/four-role cases covered elsewhere.

It does not prove the probabilistic moment bounds of Section 9.1.
-/

namespace OpenAI086

/-- Zero-based index of the FIRST failed test; none if every test passed. -/
def firstFailureIndex : List Bool → Option ℕ
  | [] => none
  | false :: _ => some 0
  | true :: bs => (firstFailureIndex bs).map Nat.succ

/-- No failed role is equivalent to success of every role. -/
theorem firstFailureIndex_none_iff_all_true (bs : List Bool) :
    firstFailureIndex bs = none ↔ ∀ b ∈ bs, b = true := by
  induction bs with
  | nil => simp [firstFailureIndex]
  | cons b bs ih =>
      cases b <;> simp [firstFailureIndex, ih]

/-- If the first `n` roles pass and the next one fails, the recorded
failure is exactly at `n`, regardless of what happens afterward. -/
theorem firstFailureIndex_true_prefix
    (n : ℕ) (tail : List Bool) :
    firstFailureIndex (List.replicate n true ++ false :: tail) = some n := by
  induction n with
  | zero => simp [firstFailureIndex]
  | succ n ih =>
      simp [List.replicate_succ, firstFailureIndex, ih]

end OpenAI086
