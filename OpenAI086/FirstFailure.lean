import Mathlib

/-!
# OpenAI #086, §9.1: first-failing-role convention

A role called the *first* failure must have all preceding roles passing;
roles after it are unrestricted. The implementation below is a finite
three-role model, not a replacement for Lemma 9.1's analytic scale count.
-/

namespace OpenAI086

/-- `true` means the role failed. -/
def firstFailure3 (bad : Fin 3 → Bool) : Option (Fin 3) :=
  if bad 0 then some 0 else if bad 1 then some 1
  else if bad 2 then some 2 else none

/-- Failure in role 1 requires role 0 to have passed. -/
theorem first_failure_one_iff (bad : Fin 3 → Bool) :
    firstFailure3 bad = some 1 ↔
      bad 0 = false ∧ bad 1 = true := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;>
    simp [firstFailure3, h0, h1]

/-- Failure in role 2 requires roles 0 and 1 to have passed. -/
theorem first_failure_two_iff (bad : Fin 3 → Bool) :
    firstFailure3 bad = some 2 ↔
      bad 0 = false ∧ bad 1 = false ∧ bad 2 = true := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;> cases h2 : bad 2 <;>
    simp [firstFailure3, h0, h1, h2]

end OpenAI086
