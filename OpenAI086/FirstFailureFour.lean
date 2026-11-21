import Mathlib

/-!
# Section 9.1: four-role first-failure masks

A trial is assigned to its first failing role. This imposes success
for all *earlier* roles, not for later roles. This file extends the
three-role finite Boolean check to the four-role case in §9.1.
It does not prove the analytic sparse-counting result in Lemma 9.1.
-/

namespace OpenAI086

/-- Return the first failing role among the four roles. -/
def firstFailure4 (bad : Fin 4 → Bool) : Option (Fin 4) :=
  if bad 0 then some 0 else if bad 1 then some 1
  else if bad 2 then some 2 else if bad 3 then some 3 else none

/-- The first role fails exactly when it is marked bad. -/
theorem first_failure_four_zero_iff (bad : Fin 4 → Bool) :
    firstFailure4 bad = some 0 ↔ bad 0 = true := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;>
    cases h2 : bad 2 <;> cases h3 : bad 3 <;>
    simp [firstFailure4, h0, h1, h2, h3]

/-- Failing at role one requires the preceding role to pass. -/
theorem first_failure_four_one_iff (bad : Fin 4 → Bool) :
    firstFailure4 bad = some 1 ↔
      bad 0 = false ∧ bad 1 = true := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;>
    cases h2 : bad 2 <;> cases h3 : bad 3 <;>
    simp [firstFailure4, h0, h1, h2, h3]

/-- Failing at role two requires roles zero and one to pass. -/
theorem first_failure_four_two_iff (bad : Fin 4 → Bool) :
    firstFailure4 bad = some 2 ↔
      bad 0 = false ∧ bad 1 = false ∧ bad 2 = true := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;>
    cases h2 : bad 2 <;> cases h3 : bad 3 <;>
    simp [firstFailure4, h0, h1, h2, h3]

/-- Failing at the final role requires all three previous roles to pass. -/
theorem first_failure_four_three_iff (bad : Fin 4 → Bool) :
    firstFailure4 bad = some 3 ↔
      bad 0 = false ∧ bad 1 = false ∧ bad 2 = false ∧ bad 3 = true := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;>
    cases h2 : bad 2 <;> cases h3 : bad 3 <;>
    simp [firstFailure4, h0, h1, h2, h3]

/-- A successful trial has no failing role. -/
theorem first_failure_four_none_iff (bad : Fin 4 → Bool) :
    firstFailure4 bad = none ↔
      bad 0 = false ∧ bad 1 = false ∧ bad 2 = false ∧ bad 3 = false := by
  cases h0 : bad 0 <;> cases h1 : bad 1 <;>
    cases h2 : bad 2 <;> cases h3 : bad 3 <;>
    simp [firstFailure4, h0, h1, h2, h3]

end OpenAI086
