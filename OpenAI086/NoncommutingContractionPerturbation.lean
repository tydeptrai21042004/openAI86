import Mathlib
import OpenAI086.NoncommutingProducts

/-!
# Lemma 3.3: an ordered, noncommutative contraction perturbation bound

The paper telescopes products of distinct (noncommuting) projection
families.  Its algebraic estimate can be stated independently for
**arbitrary contractions in a normed ring**:

  ‖A₁ ... Aₘ - B₁ ... Bₘ‖ ≤ ∑ᵢ ‖Aᵢ - Bᵢ‖.

This file proves that inequality by combining the exact noncommutative
ordered telescoping identity with contraction bounds for every suffix.
It is not the Rademacher--Menshov logarithmic square-function theorem.
-/

namespace OpenAI086

/-- The ordered product of finitely many left contractions is a contraction. -/
theorem ordered_left_contracts {R : Type*} [NormedRing R]
    (pairs : List (R × R))
    (h : ∀ p ∈ pairs, ‖p.1‖ ≤ 1) :
    ‖orderedLeft pairs‖ ≤ 1 := by
  induction pairs with
  | nil => simp [orderedLeft]
  | cons p ps ih =>
      have hp : ‖p.1‖ ≤ 1 := h p (by simp)
      have hps : ∀ q ∈ ps, ‖q.1‖ ≤ 1 := by
        intro q hq
        exact h q (by simp [hq])
      have htail := ih hps
      change ‖p.1 * orderedLeft ps‖ ≤ 1
      calc
        ‖p.1 * orderedLeft ps‖ ≤ ‖p.1‖ * ‖orderedLeft ps‖ :=
          norm_mul_le _ _
        _ ≤ ‖p.1‖ := by
          have hm := mul_le_mul_of_nonneg_left htail (norm_nonneg p.1)
          nlinarith
        _ ≤ 1 := hp

/-- The ordered product of finitely many right contractions is a contraction. -/
theorem ordered_right_contracts {R : Type*} [NormedRing R]
    (pairs : List (R × R))
    (h : ∀ p ∈ pairs, ‖p.2‖ ≤ 1) :
    ‖orderedRight pairs‖ ≤ 1 := by
  induction pairs with
  | nil => simp [orderedRight]
  | cons p ps ih =>
      have hp : ‖p.2‖ ≤ 1 := h p (by simp)
      have hps : ∀ q ∈ ps, ‖q.2‖ ≤ 1 := by
        intro q hq
        exact h q (by simp [hq])
      have htail := ih hps
      change ‖p.2 * orderedRight ps‖ ≤ 1
      calc
        ‖p.2 * orderedRight ps‖ ≤ ‖p.2‖ * ‖orderedRight ps‖ :=
          norm_mul_le _ _
        _ ≤ ‖p.2‖ := by
          have hm := mul_le_mul_of_nonneg_left htail (norm_nonneg p.2)
          nlinarith
        _ ≤ 1 := hp

/-- Every term of the ordered error budget is nonnegative. -/
theorem ordered_error_budget_nonnegative {R : Type*} [NormedRing R]
    (pairs : List (R × R)) : 0 ≤ orderedErrorBudget pairs := by
  induction pairs with
  | nil => simp [orderedErrorBudget]
  | cons p ps ih =>
      change 0 ≤ ‖p.1 - p.2‖ * ‖orderedLeft ps‖ +
        ‖p.2‖ * orderedErrorBudget ps
      exact add_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) ih)

/-- The telescoping norm budget is at most the sum of individual errors
when both lists consist of contractions. -/
theorem ordered_error_budget_of_contractions {R : Type*} [NormedRing R]
    (pairs : List (R × R))
    (hleft : ∀ p ∈ pairs, ‖p.1‖ ≤ 1)
    (hright : ∀ p ∈ pairs, ‖p.2‖ ≤ 1) :
    orderedErrorBudget pairs ≤
      (pairs.map (fun p => ‖p.1 - p.2‖)).sum := by
  induction pairs with
  | nil => simp [orderedErrorBudget]
  | cons p ps ih =>
      have hleft_ps : ∀ q ∈ ps, ‖q.1‖ ≤ 1 := by
        intro q hq
        exact hleft q (by simp [hq])
      have hright_ps : ∀ q ∈ ps, ‖q.2‖ ≤ 1 := by
        intro q hq
        exact hright q (by simp [hq])
      have hp_right : ‖p.2‖ ≤ 1 := hright p (by simp)
      have htail : ‖orderedLeft ps‖ ≤ 1 :=
        ordered_left_contracts ps hleft_ps
      have hbudget_nonneg := ordered_error_budget_nonnegative ps
      have hsuffix := ih hleft_ps hright_ps
      change ‖p.1 - p.2‖ * ‖orderedLeft ps‖ +
          ‖p.2‖ * orderedErrorBudget ps ≤
        ‖p.1 - p.2‖ + (ps.map (fun q => ‖q.1 - q.2‖)).sum
      calc
        ‖p.1 - p.2‖ * ‖orderedLeft ps‖ +
            ‖p.2‖ * orderedErrorBudget ps ≤
          ‖p.1 - p.2‖ + orderedErrorBudget ps := by
            have h1 := mul_le_mul_of_nonneg_left htail (norm_nonneg (p.1 - p.2))
            have h2 := mul_le_mul_of_nonneg_right hp_right hbudget_nonneg
            nlinarith
        _ ≤ ‖p.1 - p.2‖ +
            (ps.map (fun q => ‖q.1 - q.2‖)).sum :=
              add_le_add_left hsuffix _

/-- Noncommutative contraction perturbation, with no exponential-in-m
loss and no assumption that different factors commute. -/
theorem ordered_contraction_perturbation {R : Type*} [NormedRing R]
    (pairs : List (R × R))
    (hleft : ∀ p ∈ pairs, ‖p.1‖ ≤ 1)
    (hright : ∀ p ∈ pairs, ‖p.2‖ ≤ 1) :
    ‖orderedLeft pairs - orderedRight pairs‖ ≤
      (pairs.map (fun p => ‖p.1 - p.2‖)).sum := by
  exact (ordered_difference_norm_le pairs).trans
    (ordered_error_budget_of_contractions pairs hleft hright)

end OpenAI086
