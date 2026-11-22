import Mathlib

/-!
# Exact four-slot expansions (preparation for manuscript §5.5)

The paper separates the two earliest increments before treating the
remaining high positions. Here we prove the raw four-slot polynomial
identities, including a two-increment grouping. These identities do not
encode dyadic stopping trees or the later estimates of Proposition 5.6.
-/

namespace OpenAI086

/-- Isolate exactly the zero-, one-, and two-increment terms in two
chosen slots while holding the other two slots fixed. -/
theorem finite_two_slot_increment_expansion
    (a b da db c d : ℝ) :
    (a + da) * (b + db) * c * d =
      a * b * c * d + da * b * c * d +
      a * db * c * d + da * db * c * d := by
  ring

/-- Expand four slots by telescoping from left to right. There are
four terms, one for the earliest changed slot in this fixed order. -/
theorem finite_four_slot_first_change_expansion
    (a b c d da db dc dd : ℝ) :
    (a + da) * (b + db) * (c + dc) * (d + dd) - a * b * c * d =
      da * (b + db) * (c + dc) * (d + dd) +
      a * db * (c + dc) * (d + dd) +
      a * b * dc * (d + dd) +
      a * b * c * dd := by
  ring

/-- When two coarse slots stay fixed, moving both high slots produces
three disjoint algebraic contributions, with the double-increment term
included exactly once. -/
theorem finite_two_high_slot_error_expansion
    (a b c d dc dd : ℝ) :
    a * b * ((c + dc) * (d + dd) - c * d) =
      a * b * dc * d + a * b * c * dd + a * b * dc * dd := by
  ring

end OpenAI086
