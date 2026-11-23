import Mathlib
import OpenAI086.BadDensityBudgetAssembly

/-!
# Lemma 8.6: absorption with the automatically bad initial heights

In the manuscript the first `lag` heights are bad by definition.  The
V9–V13 arguments estimated only the remaining `H` heights.  This
module performs the **exact quantitative absorption**, retaining the
initial height cost on the correct side of the inequality.

This module is a source-level proof candidate until checked by the pinned
Lean kernel.  It is an elementary real-valued incidence lemma and does
not assume or establish any trilinear-Hilbert analytic assertion.
-/

namespace OpenAI086

/-- Suppose there are `N+1` spatial positions, `lag` automatically bad
initial heights, and `H` subsequent heights.  Every position has at
least `delta * (H+lag)` bad incidences in total.  The per-position
post-lag cost is `Q`, and the per-height across-position cost is `R`.

The paper's lower bound on the *total* height window, together with
`2*(lag+Q) <= delta*(H+lag)`, yields the unweakened final bound
`N+1 <= 2*R/delta`.  Replacing `delta` by a smaller post-lag density
would lose precisely this constant. -/
theorem bad_density_with_initial_heights
    (N H lag : ℕ) (delta Q R : ℝ)
    (vertical horizontal bad : Fin (N + 1) → Fin H → ℝ)
    (hdelta : 0 < delta) (hH : 0 < H) (hR : 0 ≤ R)
    (habsorb : 2 * ((lag : ℝ) + Q) ≤
      delta * ((H + lag : ℕ) : ℝ))
    (hlower : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) ≤
        (lag : ℝ) + ∑ h : Fin H, bad i h)
    (hpoint : ∀ i : Fin (N + 1), ∀ h : Fin H,
      bad i h ≤ vertical i h + horizontal i h)
    (hv : ∀ i : Fin (N + 1),
      (∑ h : Fin H, vertical i h) ≤ Q)
    (hh : ∀ h : Fin H,
      (∑ i : Fin (N + 1), horizontal i h) ≤ R) :
    (((N + 1 : ℕ) : ℝ)) ≤ 2 * R / delta := by
  have hupper := bad_density_two_way_budget (N + 1) H
    vertical horizontal bad Q R hpoint hv hh
  have hlowerTotal :
      (((N + 1 : ℕ) : ℝ)) *
          (delta * ((H + lag : ℕ) : ℝ)) ≤
        (((N + 1 : ℕ) : ℝ)) * (lag : ℝ) +
          ∑ i : Fin (N + 1), ∑ h : Fin H, bad i h := by
    have hs :
        (∑ _i : Fin (N + 1), delta * ((H + lag : ℕ) : ℝ)) ≤
          ∑ i : Fin (N + 1),
            ((lag : ℝ) + ∑ h : Fin H, bad i h) := by
      apply Finset.sum_le_sum
      intro i _
      exact hlower i
    simpa [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc] using hs
  have hn : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
  have habsorbN :
      (((N + 1 : ℕ) : ℝ)) * (2 * ((lag : ℝ) + Q)) ≤
        (((N + 1 : ℕ) : ℝ)) * (delta * ((H + lag : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left habsorb hn
  have hlen : (H : ℝ) ≤ ((H + lag : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right H lag)
  have hRlen : (H : ℝ) * R ≤ ((H + lag : ℕ) : ℝ) * R :=
    mul_le_mul_of_nonneg_right hlen hR
  have hscaled :
      (((N + 1 : ℕ) : ℝ) * delta) * ((H + lag : ℕ) : ℝ) ≤
        (2 * R) * ((H + lag : ℕ) : ℝ) := by
    nlinarith [hupper, hlowerTotal, habsorbN, hRlen]
  have htotalPos : (0 : ℝ) < ((H + lag : ℕ) : ℝ) := by
    have : H ≤ H + lag := Nat.le_add_right H lag
    exact_mod_cast (lt_of_lt_of_le hH this)
  have hfinal : (((N + 1 : ℕ) : ℝ) * delta) ≤ 2 * R :=
    (mul_le_mul_right htotalPos).mp hscaled
  exact (le_div_iff₀ hdelta).2 hfinal


/-- Strict form matching the strict bad-height density in manuscript
Lemma 8.6. There is at least one position because the index type is
`Fin (N+1)`. The strict lower estimate survives the finite sum. -/
theorem bad_density_with_initial_heights_strict
    (N H lag : ℕ) (delta Q R : ℝ)
    (vertical horizontal bad : Fin (N + 1) → Fin H → ℝ)
    (hdelta : 0 < delta) (hH : 0 < H) (hR : 0 ≤ R)
    (habsorb : 2 * ((lag : ℝ) + Q) ≤
      delta * ((H + lag : ℕ) : ℝ))
    (hlower : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) <
        (lag : ℝ) + ∑ h : Fin H, bad i h)
    (hpoint : ∀ i : Fin (N + 1), ∀ h : Fin H,
      bad i h ≤ vertical i h + horizontal i h)
    (hv : ∀ i : Fin (N + 1),
      (∑ h : Fin H, vertical i h) ≤ Q)
    (hh : ∀ h : Fin H,
      (∑ i : Fin (N + 1), horizontal i h) ≤ R) :
    (((N + 1 : ℕ) : ℝ)) < 2 * R / delta := by
  have hupper := bad_density_two_way_budget (N + 1) H
    vertical horizontal bad Q R hpoint hv hh
  have hlowerTotal :
      (((N + 1 : ℕ) : ℝ)) *
          (delta * ((H + lag : ℕ) : ℝ)) <
        (((N + 1 : ℕ) : ℝ)) * (lag : ℝ) +
          ∑ i : Fin (N + 1), ∑ h : Fin H, bad i h := by
    have hs :
        (∑ _i : Fin (N + 1), delta * ((H + lag : ℕ) : ℝ)) <
          ∑ i : Fin (N + 1),
            ((lag : ℝ) + ∑ h : Fin H, bad i h) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact le_of_lt (hlower i)
      · refine ⟨⟨0, Nat.zero_lt_succ N⟩, Finset.mem_univ _, ?_⟩
        exact hlower ⟨0, Nat.zero_lt_succ N⟩
    simpa [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc] using hs
  have hn : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
  have habsorbN :
      (((N + 1 : ℕ) : ℝ)) * (2 * ((lag : ℝ) + Q)) ≤
        (((N + 1 : ℕ) : ℝ)) * (delta * ((H + lag : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left habsorb hn
  have hlen : (H : ℝ) ≤ ((H + lag : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right H lag)
  have hRlen : (H : ℝ) * R ≤ ((H + lag : ℕ) : ℝ) * R :=
    mul_le_mul_of_nonneg_right hlen hR
  have hscaled :
      (((N + 1 : ℕ) : ℝ) * delta) * ((H + lag : ℕ) : ℝ) <
        (2 * R) * ((H + lag : ℕ) : ℝ) := by
    nlinarith [hupper, hlowerTotal, habsorbN, hRlen]
  have htotalPos : (0 : ℝ) < ((H + lag : ℕ) : ℝ) := by
    have : H ≤ H + lag := Nat.le_add_right H lag
    exact_mod_cast (lt_of_lt_of_le hH this)
  have hfinal : (((N + 1 : ℕ) : ℝ) * delta) < 2 * R :=
    (mul_lt_mul_right htotalPos).mp hscaled
  exact (lt_div_iff₀ hdelta).2 hfinal

end OpenAI086
