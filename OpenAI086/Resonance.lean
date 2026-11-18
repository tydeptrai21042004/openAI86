import Mathlib

/-!
OpenAI #086, Introduction (pp. 2–3): the exact degree-two resonance
for the four progression positions x, x+t, x+2t, x+3t.

All results below are proved independently, using polynomial normalization.
They are algebraic inputs, NOT a proof of the L³ → L¹ bound.
-/

namespace OpenAI086

/-- Cancellation of constant-phase coefficients. -/
theorem zeroth_moment : (-1 : ℝ) + 3 - 3 + 1 = 0 := by
  norm_num

/-- The four-node relation annihilates every affine phase. -/
theorem first_moment (x t : ℝ) :
    -x + 3 * (x + t) - 3 * (x + 2 * t) + (x + 3 * t) = 0 := by
  ring

/-- Exact quadratic resonance in the introduction of OpenAI #086. -/
theorem quadratic_resonance (x t : ℝ) :
    -(x ^ 2) + 3 * (x + t) ^ 2 - 3 * (x + 2 * t) ^ 2 +
      (x + 3 * t) ^ 2 = 0 := by
  ring

/-- The four-node third finite difference: degree three does not cancel. -/
theorem cubic_difference (x t : ℝ) :
    -(x ^ 3) + 3 * (x + t) ^ 3 - 3 * (x + 2 * t) ^ 3 +
      (x + 3 * t) ^ 3 = 6 * t ^ 3 := by
  ring

/-- Degree-three cancellation, unlike degree-two cancellation, is false. -/
theorem cubic_cancellation_is_false :
    ¬ (∀ x t : ℝ,
        -(x ^ 3) + 3 * (x + t) ^ 3 - 3 * (x + 2 * t) ^ 3 +
          (x + 3 * t) ^ 3 = 0) := by
  intro h
  have h01 := h 0 1
  norm_num at h01

/-- All degree-two resonance weights for this progression are multiples
of (-1, 3, -3, 1). Here c3 is the free scalar. -/
theorem quadratic_weights_unique
    (c0 c1 c2 c3 : ℝ)
    (h : ∀ x t : ℝ,
      c0 * x ^ 2 + c1 * (x + t) ^ 2 + c2 * (x + 2 * t) ^ 2 +
        c3 * (x + 3 * t) ^ 2 = 0) :
    c0 = -c3 ∧ c1 = 3 * c3 ∧ c2 = -3 * c3 := by
  have h10 := h 1 0
  have h01 := h 0 1
  have h11 := h 1 1
  norm_num at h10 h01 h11
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end OpenAI086
