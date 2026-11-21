import Mathlib
import OpenAI086.BadDensityIncidence

/-!
# Lemma 8.6: assembling the two incidence budgets

The proof on page 70 separates bad incidences into (a) those which can be
charged to one spatial position and (b) those which can be charged to one
height. This file proves the exact double-counting/absorption step for a
finite matrix of real incidences, *without assuming its aggregate bound*.

`vertical` groups the initial heights, within-position logarithmic jumps,
and within-position height-exceptional density. `horizontal` groups the
cross-position logarithmic gaps and exceptional-primary density.

The required individual bounds on `vertical` and `horizontal` still need
to be established from the full nested finite sets of Lemma 8.6. Hence this
is an intermediate proof, NOT a formalization of the entire Lemma 8.6.
-/

namespace OpenAI086

/-- Fubini-style assembly of per-position and per-height finite budgets. -/
theorem bad_density_two_way_budget
    (N H : ℕ) (vertical horizontal bad : Fin N → Fin H → ℝ)
    (Q R : ℝ)
    (hpoint : ∀ i : Fin N, ∀ h : Fin H,
       bad i h ≤ vertical i h + horizontal i h)
    (hv : ∀ i : Fin N, (∑ h : Fin H, vertical i h) ≤ Q)
    (hh : ∀ h : Fin H, (∑ i : Fin N, horizontal i h) ≤ R) :
    (∑ i : Fin N, ∑ h : Fin H, bad i h) ≤
        (N : ℝ) * Q + (H : ℝ) * R := by
  have hvertical :
      (∑ i : Fin N, ∑ h : Fin H, vertical i h) ≤ (N : ℝ) * Q := by
    calc
      (∑ i : Fin N, ∑ h : Fin H, vertical i h) ≤
          ∑ _i : Fin N, Q := by
            apply Finset.sum_le_sum
            intro i _
            exact hv i
      _ = (N : ℝ) * Q := by simp
  have hhorizontal :
      (∑ h : Fin H, ∑ i : Fin N, horizontal i h) ≤ (H : ℝ) * R := by
    calc
      (∑ h : Fin H, ∑ i : Fin N, horizontal i h) ≤
          ∑ _h : Fin H, R := by
            apply Finset.sum_le_sum
            intro h _
            exact hh h
      _ = (H : ℝ) * R := by simp
  have hpointwise :
      (∑ i : Fin N, ∑ h : Fin H, bad i h) ≤
        (∑ i : Fin N, ∑ h : Fin H,
          (vertical i h + horizontal i h)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro h _
    exact hpoint i h
  have hcomm :
      (∑ i : Fin N, ∑ h : Fin H, horizontal i h) =
        (∑ h : Fin H, ∑ i : Fin N, horizontal i h) := by
    exact Finset.sum_comm
  have hsplit :
      (∑ i : Fin N, ∑ h : Fin H, (vertical i h + horizontal i h)) =
        (∑ i : Fin N, ∑ h : Fin H, vertical i h) +
          (∑ h : Fin H, ∑ i : Fin N, horizontal i h) := by
    simp only [Finset.sum_add_distrib]
    rw [hcomm]
  rw [hsplit] at hpointwise
  linarith

/-- The quantitative chain-length estimate from the *separate* incidence
budgets. The last absorption step is no longer an external hypothesis. -/
theorem bad_density_chain_from_two_budgets
    (N H : ℕ) (δ Q R : ℝ)
    (vertical horizontal bad : Fin N → Fin H → ℝ)
    (hδ : 0 < δ) (hH : 0 < H)
    (hbudget : 2 * Q ≤ δ * (H : ℝ))
    (hlower : ∀ i : Fin N,
      δ * (H : ℝ) ≤ ∑ h : Fin H, bad i h)
    (hpoint : ∀ i : Fin N, ∀ h : Fin H,
       bad i h ≤ vertical i h + horizontal i h)
    (hv : ∀ i : Fin N, (∑ h : Fin H, vertical i h) ≤ Q)
    (hh : ∀ h : Fin H, (∑ i : Fin N, horizontal i h) ≤ R) :
    (N : ℝ) ≤ 2 * R / δ := by
  apply bad_density_incidence_chain_bound N H δ Q R bad hδ hH
    hbudget hlower
  exact bad_density_two_way_budget N H vertical horizontal bad
    Q R hpoint hv hh

end OpenAI086
