import Mathlib
import OpenAI086.HeightLagTelescoping
import OpenAI086.BadDensityBudgetAssembly

/-!
# Lemma 8.6: both axes of logarithmic-gap telescoping

The paper's bad-density count has TWO different telescoping directions:
  * height lag, within a fixed spatial position;
  * position gap, at a fixed height, between interleaved P and C families.

This module proves BOTH algebraic budgets and combines them with finite
incidence double-counting.  Unlike V9, the per-height interleaved-gap
budget is no longer assumed: it is derived from the precise endpoint
inclusions that are missing at the last position in the PDF.

Two independent exceptional-primary incidence budgets remain hypotheses,
not hidden theorems.  They are the next part of the actual Lemma 8.6.
The assertions are REAL scalar floor-log models, not claims about the
full variable finite sets or about Theorem 1.1.
-/

namespace OpenAI086

/-- Noncommutative or algebraic hypotheses are not involved: the sum of
interleaved scalar gaps telescopes if each C-position fits into the
next P-position.  There are N+1 positions, indexed 0 through N. -/
theorem real_interleaved_gap_telescope (N : ℕ) (p c : ℕ → ℝ)
    (hchain : ∀ i < N, c i ≤ p (i + 1)) :
    (∑ i ∈ Finset.range (N + 1), (c i - p i)) ≤ c N - p 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hprefix :
          (∑ i ∈ Finset.range (n + 1), (c i - p i)) ≤ c n - p 0 :=
        ih (fun i hi => hchain i (by omega))
      have hstep : c n ≤ p (n + 1) := hchain n (by omega)
      rw [Finset.sum_range_succ]
      linarith

/-- An explicit terminal inclusion `P_N ⊆ C_N` is required for the
actual paper's nonnegative gaps.  The upper bound itself also requires
the first P-count to be nonnegative and the final C-count bounded. -/
theorem real_interleaved_gap_budget
    (N : ℕ) (p c : ℕ → ℝ) (L : ℝ)
    (hpc : ∀ i ≤ N, p i ≤ c i)
    (hcp : ∀ i < N, c i ≤ p (i + 1))
    (hfirst : 0 ≤ p 0) (hlast : c N ≤ L) :
    (∑ i ∈ Finset.range (N + 1), (c i - p i)) ≤ L := by
  have hgap := real_interleaved_gap_telescope N p c hcp
  linarith

/-- A full two-direction *scalar* bad-density bound. The vertical
logarithmic jump `p(i,h+lag)-p(i,h)` and horizontal gap
`c(i,h+lag)-p(i,h+lag)` are each bounded by ACTUAL telescoping, rather
than a separately assumed total.  Only the exceptional incidences
`heightNoise` and `positionNoise` remain to be proved from label ranks.

`N+1` is the number of spatial chain positions, and `H` is the number
of tested heights (after the initial lag).  The lemma uses a non-strict
conclusion because the lower incidence assumption is non-strict. -/
theorem bad_density_chain_with_both_telescopes
    (N H lag : ℕ) (δ L A B : ℝ)
    (p c : ℕ → ℕ → ℝ)
    (heightNoise positionNoise bad : Fin (N + 1) → Fin H → ℝ)
    (hδ : 0 < δ) (hH : 0 < H)
    (hpc : ∀ i ≤ N, ∀ h, p i h ≤ c i h)
    (hcp : ∀ i < N, ∀ h, c i h ≤ p (i + 1) h)
    (hfirstHeight : ∀ i ≤ N, ∀ r < lag, 0 ≤ p i r)
    (hlastHeight : ∀ i ≤ N, ∀ r < lag, p i (H + r) ≤ L)
    (hfirstPosition : ∀ h < H, 0 ≤ p 0 (h + lag))
    (hlastPosition : ∀ h < H, c N (h + lag) ≤ L)
    (hheightNoise : ∀ i : Fin (N + 1),
      (∑ h : Fin H, heightNoise i h) ≤ A)
    (hpositionNoise : ∀ h : Fin H,
      (∑ i : Fin (N + 1), positionNoise i h) ≤ B)
    (hpoint : ∀ i : Fin (N + 1), ∀ h : Fin H,
      bad i h ≤
        ((p i.val (h.val + lag) - p i.val h.val) + heightNoise i h) +
        ((c i.val (h.val + lag) - p i.val (h.val + lag)) +
          positionNoise i h))
    (hlower : ∀ i : Fin (N + 1),
      δ * (H : ℝ) ≤ ∑ h : Fin H, bad i h)
    (hbudget : 2 * ((lag : ℝ) * L + A) ≤ δ * (H : ℝ)) :
    ((N + 1 : ℕ) : ℝ) ≤ 2 * (L + B) / δ := by
  let vertical : Fin (N + 1) → Fin H → ℝ := fun i h =>
    (p i.val (h.val + lag) - p i.val h.val) + heightNoise i h
  let horizontal : Fin (N + 1) → Fin H → ℝ := fun i h =>
    (c i.val (h.val + lag) - p i.val (h.val + lag)) + positionNoise i h
  have hv : ∀ i : Fin (N + 1),
      (∑ h : Fin H, vertical i h) ≤ (lag : ℝ) * L + A := by
    intro i
    have hlag := finite_height_lag_budget (p i.val) lag H L
      (hfirstHeight i.val (by omega))
      (hlastHeight i.val (by omega))
    have hident :
        (∑ h : Fin H, (p i.val (h.val + lag) - p i.val h.val)) =
        ∑ h ∈ Finset.range H, (p i.val (h + lag) - p i.val h) := by
      exact Fin.sum_univ_eq_sum_range
        (fun h : ℕ => p i.val (h + lag) - p i.val h) H
    simp only [vertical, Finset.sum_add_distrib]
    rw [hident]
    have hn := hheightNoise i
    linarith
  have hh : ∀ h : Fin H,
      (∑ i : Fin (N + 1), horizontal i h) ≤ L + B := by
    intro h
    have hgap := real_interleaved_gap_budget N
      (fun i => p i (h.val + lag)) (fun i => c i (h.val + lag)) L
      (fun i hi => hpc i hi (h.val + lag))
      (fun i hi => hcp i hi (h.val + lag))
      (hfirstPosition h.val h.isLt)
      (hlastPosition h.val h.isLt)
    have hident :
        (∑ i : Fin (N + 1),
          (c i.val (h.val + lag) - p i.val (h.val + lag))) =
        ∑ i ∈ Finset.range (N + 1),
          (c i (h.val + lag) - p i (h.val + lag)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i : ℕ => c i (h.val + lag) - p i (h.val + lag)) (N + 1)
    simp only [horizontal, Finset.sum_add_distrib]
    rw [hident]
    have hn := hpositionNoise h
    linarith
  exact bad_density_chain_from_two_budgets (N + 1) H δ
    ((lag : ℝ) * L + A) (L + B) vertical horizontal bad
    hδ hH hbudget hlower (by
      intro i h
      exact hpoint i h) hv hh

end OpenAI086
