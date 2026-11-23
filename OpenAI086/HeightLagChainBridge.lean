import Mathlib
import OpenAI086.HeightLagTelescoping
import OpenAI086.BadDensityBudgetAssembly

/-!
# A new, nontrivial portion of the actual Lemma 8.6 counting proof

This theorem no longer assumes the *per-position* incidence budget Q:
it is DERIVED from the exact height-lag telescoping identity and a
separately identified height-exception incidence bound. The remaining
per-height budget corresponds to the interleaved position gaps and
exceptional primary rank counting, which must still be linked to the
actual varying finite sets of the paper.

`H` is the number of later heights (the initial `lag` heights are to be
accounted for in the caller's vertical error budget if present).
-/

namespace OpenAI086

/-- A directly usable chain-length estimate with the height-lag term
proved, not placed in an upstream hypothesis. The only residual global
counting budget is per-height, not per-position. -/
theorem bad_density_chain_with_proved_height_lag
    (N H lag : ℕ) (δ L A R : ℝ)
    (p : Fin N → ℕ → ℝ)
    (heightNoise horizontal bad : Fin N → Fin H → ℝ)
    (hδ : 0 < δ) (hH : 0 < H)
    (hfirst : ∀ i : Fin N, ∀ r < lag, 0 ≤ p i r)
    (hlast : ∀ i : Fin N, ∀ r < lag, p i (H + r) ≤ L)
    (hnoise : ∀ i : Fin N,
      (∑ h : Fin H, heightNoise i h) ≤ A)
    (hhorizontal : ∀ h : Fin H,
      (∑ i : Fin N, horizontal i h) ≤ R)
    (hpoint : ∀ i : Fin N, ∀ h : Fin H,
      bad i h ≤ (p i (h.val + lag) - p i h.val) +
        heightNoise i h + horizontal i h)
    (hlower : ∀ i : Fin N,
      δ * (H : ℝ) ≤ ∑ h : Fin H, bad i h)
    (hbudget : 2 * ((lag : ℝ) * L + A) ≤ δ * (H : ℝ)) :
    (N : ℝ) ≤ 2 * R / δ := by
  let vertical : Fin N → Fin H → ℝ := fun i h =>
    (p i (h.val + lag) - p i h.val) + heightNoise i h
  have hvertical : ∀ i : Fin N,
      (∑ h : Fin H, vertical i h) ≤ (lag : ℝ) * L + A := by
    intro i
    have hlag := finite_height_lag_budget (p i) lag H L
      (hfirst i) (hlast i)
    have hident :
        (∑ h : Fin H, (p i (h.val + lag) - p i h.val)) =
        ∑ h ∈ Finset.range H, (p i (h + lag) - p i h) := by
      exact Fin.sum_univ_eq_sum_range
        (fun h : ℕ => p i (h + lag) - p i h) H
    simp only [vertical, Finset.sum_add_distrib]
    have hn := hnoise i
    rw [hident]
    linarith
  apply bad_density_chain_from_two_budgets N H δ
    ((lag : ℝ) * L + A) R vertical horizontal bad
    hδ hH hbudget hlower
  · intro i h
    exact hpoint i h
  · exact hvertical
  · exact hhorizontal

end OpenAI086
