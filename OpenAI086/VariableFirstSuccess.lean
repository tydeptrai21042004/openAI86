import Mathlib

/-!
# Nonstationary first-success identities for the mode-height selection (§9.1)

The manuscript samples heights until the first height where every chosen
mode is good.  The finite-horizon probability bookkeeping does **not**
require identical success probabilities.  This file proves the exact
identity for an arbitrary sequence of conditional failure probabilities,
and obtains uniform exponential survival bounds whenever those probabilities
are bounded by a common `r < 1`.

No independence, mode coherence, or analytic distributional claim is smuggled
into these lemmas.  The application to mode masks in §9.1 is still open.
-/

namespace OpenAI086

/-- Survival mass after `N` consecutive failures, allowing a different
conditional failure probability at every trial. -/
def variableFailureSurvival (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => variableFailureSurvival q n * q n

/-- The mass of a first success at trial `n`. -/
def variableFirstSuccessMass (q : ℕ → ℝ) (n : ℕ) : ℝ :=
  variableFailureSurvival q n * (1 - q n)

/-- One-step conservation of mass, with no stochastic assumptions beyond
the scalar conditional failure weights. -/
theorem variable_success_mass_step (q : ℕ → ℝ) (n : ℕ) :
    variableFirstSuccessMass q n + variableFailureSurvival q (n + 1) =
      variableFailureSurvival q n := by
  simp only [variableFirstSuccessMass, variableFailureSurvival]
  ring

/-- Exact finite identity: first-success masses plus the mass of having
failed all `N` trials are one.  No limit or normalization is omitted. -/
theorem variable_first_success_identity (q : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, variableFirstSuccessMass q n) +
      variableFailureSurvival q N = 1 := by
  induction N with
  | zero => simp [variableFailureSurvival]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep := variable_success_mass_step q N
      linarith

/-- Survival is nonnegative under bona fide failure probabilities. -/
theorem variable_survival_nonnegative (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n) (N : ℕ) :
    0 ≤ variableFailureSurvival q N := by
  induction N with
  | zero => simp [variableFailureSurvival]
  | succ N ih =>
      change 0 ≤ variableFailureSurvival q N * q N
      exact mul_nonneg ih (hq N)

/-- Bounding every trial's failure probability by `r` yields the sharp
uniform product bound. In particular this does not grow with N. -/
theorem variable_survival_le_geometric (q : ℕ → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hq0 : ∀ n, 0 ≤ q n)
    (hqmax : ∀ n, q n ≤ r) (N : ℕ) :
    variableFailureSurvival q N ≤ r ^ N := by
  induction N with
  | zero => simp [variableFailureSurvival]
  | succ N ih =>
      calc
        variableFailureSurvival q (N + 1) =
            variableFailureSurvival q N * q N := rfl
        _ ≤ r ^ N * q N :=
            mul_le_mul_of_nonneg_right ih (hq0 N)
        _ ≤ r ^ N * r :=
            mul_le_mul_of_nonneg_left (hqmax N) (pow_nonneg hr N)
        _ = r ^ (N + 1) := by rw [pow_succ]

/-- Finite first-success probability is at most one. -/
theorem variable_first_success_le_one (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n) (N : ℕ) :
    (∑ n ∈ Finset.range N, variableFirstSuccessMass q n) ≤ 1 := by
  have hmass := variable_first_success_identity q N
  have hsurv := variable_survival_nonnegative q hq N
  linarith

/-- A non-stationary first-success process with common failure bound
`r` has succeeded by time N with mass at least `1 - r^N`. -/
theorem variable_first_success_ge_one_sub_geometric
    (q : ℕ → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hq0 : ∀ n, 0 ≤ q n)
    (hqmax : ∀ n, q n ≤ r) (N : ℕ) :
    1 - r ^ N ≤ ∑ n ∈ Finset.range N, variableFirstSuccessMass q n := by
  have hmass := variable_first_success_identity q N
  have hsurv := variable_survival_le_geometric q r hr hq0 hqmax N
  linarith

end OpenAI086
