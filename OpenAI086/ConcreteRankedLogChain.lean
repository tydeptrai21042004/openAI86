import Mathlib
import OpenAI086.ConcreteIntegerLogBadDensity
import OpenAI086.ConcreteRankedIncidences

/-!
# Lemma 8.6: one concrete two-axis counting bridge

This theorem now derives BOTH exceptional-fraction budgets from
per-label occurrence counts and first-entry rank-size conditions,
AND instantiates the paper's rank using integer base-11/10 bins.
It therefore no longer takes (a) an abstract bad-height pointwise
inequality, (b) an unspecified rank function or (c) aggregate
exceptional-fraction budgets as hypotheses.

The remaining hypotheses are material: suitable first-entry ranks
must be constructed for the actual varying label lists, the positive
bad-height density is an upstream hypothesis, and the numerical
absorption condition must be satisfied. This is still a FINITE real
counting bridge, not the full analytic proof of Lemma 8.6 or 1.1.
-/

namespace OpenAI086

/-- Concrete two-axis rank counting with the paper's union bad-height
predicate and exact base-1.1 cardinality bins. Per-primary incidence
bounds replace both formerly postulated aggregate fraction bounds.

The explicit `r.val+1 ≤ card` hypotheses identify the first-entry
rank obligation; in applications, that rank must be assigned separately
on the two increasing axes if their entry orders differ. -/
theorem concrete_ranked_integer_log_chain
    (N H lag M : ℕ) (beta delta A B : ℝ)
    (P C : ℕ → ℕ → Finset (Fin M))
    (X : Fin (N + 1) → Finset (Fin M))
    (Y : Fin (N + 1) → Fin H → Finset (Fin M))
    (hbeta : 0 < beta) (hdelta : 0 < delta) (hH : 0 < H)
    (hheight : ∀ i ≤ N, Monotone (P i))
    (hpc : ∀ i ≤ N, ∀ h, P i h ⊆ C i h)
    (hcp : ∀ i < N, ∀ h, C i h ⊆ P (i + 1) h)
    (hheightRank : ∀ i : Fin (N + 1), ∀ h : Fin H,
      ∀ r : Fin M, r ∈ Y i h ∩ C i.val (h.val + lag) →
      r.val + 1 ≤ (C i.val (h.val + lag)).card)
    (hpositionRank : ∀ h : Fin H, ∀ i : Fin (N + 1),
      ∀ r : Fin M, r ∈ X i ∩ C i.val (h.val + lag) →
      r.val + 1 ≤ (C i.val (h.val + lag)).card)
    (hheightMultiplicity : ∀ i : Fin (N + 1), ∀ r : Fin M,
      (∑ h : Fin H,
        if r ∈ Y i h ∩ C i.val (h.val + lag) then (1 : ℝ) else 0) ≤ A)
    (hpositionMultiplicity : ∀ h : Fin H, ∀ r : Fin M,
      (∑ i : Fin (N + 1),
        if r ∈ X i ∩ C i.val (h.val + lag) then (1 : ℝ) else 0) ≤ B)
    (hbad : ∀ i : Fin (N + 1),
      delta * (H : ℝ) ≤
        ∑ h : Fin H,
          paperUnionBadHeight integerLogBin11_10 (P i.val h.val)
            (C i.val (h.val + lag)) (X i) (Y i h) beta)
    (hbudget :
      2 * ((lag : ℝ) * (integerLogBin11_10 M : ℝ) +
        A * finiteRankHarmonic M / beta) ≤ delta * (H : ℝ)) :
    ((N + 1 : ℕ) : ℝ) ≤
      2 * ((integerLogBin11_10 M : ℝ) +
        B * finiteRankHarmonic M / beta) / delta := by
  classical
  have hY : ∀ i : Fin (N + 1),
      (∑ h : Fin H,
        (((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
          ((C i.val (h.val + lag)).card : ℝ))) ≤
        A * finiteRankHarmonic M := by
    intro i
    exact concrete_exceptional_fraction_from_rank
      (fun h : Fin H => C i.val (h.val + lag))
      (fun h : Fin H => Y i h) A
      (fun h r hr => hheightRank i h r hr)
      (fun r => hheightMultiplicity i r)
  have hX : ∀ h : Fin H,
      (∑ i : Fin (N + 1),
        (((X i ∩ C i.val (h.val + lag)).card : ℝ) /
          ((C i.val (h.val + lag)).card : ℝ))) ≤
        B * finiteRankHarmonic M := by
    intro h
    exact concrete_exceptional_fraction_from_rank
      (fun i : Fin (N + 1) => C i.val (h.val + lag))
      X B
      (fun i r hr => hpositionRank h i r hr)
      (fun r => hpositionMultiplicity h r)
  exact concrete_integer_log_bad_density_chain
    N H lag M beta delta
    (A * finiteRankHarmonic M) (B * finiteRankHarmonic M)
    P C X Y hbeta hdelta hH hheight hpc hcp
    (by intro i hi h; simpa using (Finset.card_le_univ (C i h)))
    hY hX hbad hbudget

end OpenAI086
