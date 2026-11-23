import Mathlib
import OpenAI086.InitialHeightAbsorption
import OpenAI086.ConcreteChronologicalLogChain

/-!
# Full-height-window finite counterpart of manuscript Lemma 8.6

The previous chronological theorem checked only the post-lag tests.
Here the first `lag` heights are charged **as automatically bad**, and
the density and absorption use the manuscript's full `H + lag` window.

The two harmonic incidence budgets follow from actual nested sets via
`finite_chronological_harmonic_density`; rank permutations are *not*
assumptions.  The finite cardinality ranks use exact integer arithmetic
for the paper's base `11/10`.  The lemma's endpoint inclusion for the
last position, omitted in the PDF, is stated explicitly.

The source remains an uncompiled candidate until Lean/Lake is available.
-/

namespace OpenAI086

/-- Post-lag quantitative statement using a **full-window** bad-height
lower bound, rather than the weaker post-lag density used in V13.

`H` is the number of indices at or after the lag; `H+lag` is precisely
the number of heights in the original assertion. `N+1` is the number
of spatial positions. Exceptional-primary multiplicity is counted over
spatial positions; height-bad multiplicity is counted over heights.
Both sets are ranked chronologically from the evolving `C`-lists.

The conclusion is an exact finite set combinatorial counterpart to the
chain-length estimate, provided the paper's total bad-height hypothesis
and the required quantitative budget hold.  Analytic arguments establishing
these hypotheses in the actual THT application are separate obligations. -/
theorem full_chronological_integer_log_bad_density
    (N H lag M : ℕ) (beta delta A B : ℝ)
    (P C : ℕ → ℕ → Finset (Fin M))
    (X : Fin (N + 1) → Finset (Fin M))
    (Y : Fin (N + 1) → Fin H → Finset (Fin M))
    (hbeta : 0 < beta) (hdelta : 0 < delta) (hH : 0 < H)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hPheight : ∀ i ≤ N, Monotone (P i))
    (hCheight : ∀ i ≤ N, Monotone (C i))
    (hpc : ∀ i ≤ N, ∀ h, P i h ⊆ C i h)
    (hcp : ∀ i < N, ∀ h, C i h ⊆ P (i + 1) h)
    (hheightMultiplicity : ∀ i : Fin (N + 1), ∀ r : Fin M,
      (∑ h : Fin H,
        if r ∈ Y i h ∩ C i.val (h.val + lag) then (1 : ℝ) else 0) ≤ A)
    (hpositionMultiplicity : ∀ h : Fin H, ∀ r : Fin M,
      (∑ i : Fin (N + 1),
        if r ∈ X i ∩ C i.val (h.val + lag) then (1 : ℝ) else 0) ≤ B)
    (hfullBad : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) ≤ (lag : ℝ) +
        ∑ h : Fin H,
          paperUnionBadHeight integerLogBin11_10 (P i.val h.val)
            (C i.val (h.val + lag)) (X i) (Y i h) beta)
    (habsorb :
      2 * ((lag : ℝ) * ((integerLogBin11_10 M : ℕ) : ℝ) +
        (lag : ℝ) + A * finiteRankHarmonic M / beta) ≤
        delta * ((H + lag : ℕ) : ℝ)) :
    (((N + 1 : ℕ) : ℝ)) ≤
      2 * (((integerLogBin11_10 M : ℕ) : ℝ) +
        B * finiteRankHarmonic M / beta) / delta := by
  classical
  let L : ℝ := (integerLogBin11_10 M : ℝ)
  let p : ℕ → ℕ → ℝ := fun i h => (integerLogBin11_10 (P i h).card : ℝ)
  let c : ℕ → ℕ → ℝ := fun i h => (integerLogBin11_10 (C i h).card : ℝ)
  let noiseY : Fin (N + 1) → Fin H → ℝ := fun i h =>
    ((((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
      ((C i.val (h.val + lag)).card : ℝ)) / beta)
  let noiseX : Fin (N + 1) → Fin H → ℝ := fun i h =>
    ((((X i ∩ C i.val (h.val + lag)).card : ℝ) /
      ((C i.val (h.val + lag)).card : ℝ)) / beta)
  let bad : Fin (N + 1) → Fin H → ℝ := fun i h =>
    paperUnionBadHeight integerLogBin11_10 (P i.val h.val)
      (C i.val (h.val + lag)) (X i) (Y i h) beta
  have hY : ∀ i : Fin (N + 1),
      (∑ h : Fin H,
        (((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
          ((C i.val (h.val + lag)).card : ℝ))) ≤
        A * finiteRankHarmonic M := by
    intro i
    apply finite_chronological_harmonic_density
      (fun h : Fin H => C i.val (h.val + lag))
      (fun h : Fin H => Y i h)
    · intro a b hab
      exact hCheight i.val (by omega)
        (Nat.add_le_add_right (show a.val ≤ b.val from hab) lag)
    · exact hheightMultiplicity i
  have hX : ∀ h : Fin H,
      (∑ i : Fin (N + 1),
        (((X i ∩ C i.val (h.val + lag)).card : ℝ) /
          ((C i.val (h.val + lag)).card : ℝ))) ≤
        B * finiteRankHarmonic M := by
    intro h
    apply finite_chronological_harmonic_density
      (fun i : Fin (N + 1) => C i.val (h.val + lag))
      (fun i : Fin (N + 1) => X i)
    · exact interleaved_C_position_mono P C hpc hcp (h.val + lag)
    · exact hpositionMultiplicity h
  have hpcle : ∀ i ≤ N, ∀ h, p i h ≤ c i h := by
    intro i hi h
    dsimp [p, c]
    exact_mod_cast finite_set_rank_monotone integerLogBin11_10
      integer_log_bin_11_10_monotone (P i h) (C i h) (hpc i hi h)
  have hcple : ∀ i < N, ∀ h, c i h ≤ p (i + 1) h := by
    intro i hi h
    dsimp [p, c]
    exact_mod_cast finite_set_rank_monotone integerLogBin11_10
      integer_log_bin_11_10_monotone (C i h) (P (i + 1) h) (hcp i hi h)
  have hfirstH : ∀ i ≤ N, ∀ r < lag, 0 ≤ p i r := by
    intro i _ r _
    dsimp [p]
    positivity
  have hlastH : ∀ i ≤ N, ∀ r < lag, p i (H + r) ≤ L := by
    intro i hi r _
    have hs : (C i (H + r)).card ≤ M := Finset.card_le_univ _
    have hb := integer_log_bin_card_le (C i (H + r)) M hs
    exact (hpcle i hi (H + r)).trans (by exact_mod_cast hb)
  have hfirstPos : ∀ h < H, 0 ≤ p 0 (h + lag) := by
    intro h _
    dsimp [p]
    positivity
  have hlastPos : ∀ h < H, c N (h + lag) ≤ L := by
    intro h _
    have hs : (C N (h + lag)).card ≤ M := Finset.card_le_univ _
    exact_mod_cast integer_log_bin_card_le (C N (h + lag)) M hs
  have hnoiseY : ∀ i : Fin (N + 1),
      (∑ h : Fin H, noiseY i h) ≤
      A * finiteRankHarmonic M / beta := by
    intro i
    change (∑ h : Fin H,
      ((((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
        ((C i.val (h.val + lag)).card : ℝ)) / beta)) ≤
      A * finiteRankHarmonic M / beta
    rw [Finset.sum_div]
    exact div_le_div_of_nonneg_right (hY i) (le_of_lt hbeta)
  have hnoiseX : ∀ h : Fin H,
      (∑ i : Fin (N + 1), noiseX i h) ≤
      B * finiteRankHarmonic M / beta := by
    intro h
    change (∑ i : Fin (N + 1),
      ((((X i ∩ C i.val (h.val + lag)).card : ℝ) /
        ((C i.val (h.val + lag)).card : ℝ)) / beta)) ≤
      B * finiteRankHarmonic M / beta
    rw [Finset.sum_div]
    exact div_le_div_of_nonneg_right (hX h) (le_of_lt hbeta)
  have hpoint : ∀ i : Fin (N + 1), ∀ h : Fin H,
      bad i h ≤
        ((p i.val (h.val + lag) - p i.val h.val) + noiseY i h) +
        ((c i.val (h.val + lag) - p i.val (h.val + lag)) +
          noiseX i h) := by
    intro i h
    have hmono : P i.val h.val ⊆ P i.val (h.val + lag) :=
      (hPheight i.val (by omega)) (Nat.le_add_right h.val lag)
    have hmain := paper_union_bad_height_pointwise integerLogBin11_10
      integer_log_bin_11_10_monotone
      (P i.val h.val) (P i.val (h.val + lag))
      (C i.val (h.val + lag)) (X i) (Y i h)
      hmono (hpc i.val (by omega) (h.val + lag)) beta hbeta
    dsimp [bad, p, c, noiseY, noiseX]
    rw [add_div] at hmain
    linarith
  have hbad' : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) ≤
        (lag : ℝ) + ∑ h : Fin H, bad i h := hfullBad
  have hR : 0 ≤ L + B * finiteRankHarmonic M / beta := by
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hhm : 0 ≤ finiteRankHarmonic M := by
      unfold finiteRankHarmonic
      positivity
    exact add_nonneg hL (div_nonneg (mul_nonneg hB hhm) (le_of_lt hbeta))
  have habsorb' :
      2 * ((lag : ℝ) + ((lag : ℝ) * L +
        A * finiteRankHarmonic M / beta)) ≤
      delta * ((H + lag : ℕ) : ℝ) := by
    dsimp [L]
    linarith [habsorb]
  exact bad_density_with_initial_heights
    N H lag delta ((lag : ℝ) * L + A * finiteRankHarmonic M / beta)
    (L + B * finiteRankHarmonic M / beta)
    (fun i h => (p i.val (h.val + lag) - p i.val h.val) + noiseY i h)
    (fun i h => (c i.val (h.val + lag) - p i.val (h.val + lag)) + noiseX i h)
    bad hdelta hH hR habsorb' hbad' hpoint
    (by
      intro i
      have hlag := finite_height_lag_budget (p i.val) lag H L
        (hfirstH i.val (by omega)) (hlastH i.val (by omega))
      have hident :
          (∑ h : Fin H, (p i.val (h.val + lag) - p i.val h.val)) =
          ∑ h ∈ Finset.range H, (p i.val (h + lag) - p i.val h) := by
        exact Fin.sum_univ_eq_sum_range
          (fun h : ℕ => p i.val (h + lag) - p i.val h) H
      simp only [Finset.sum_add_distrib]
      rw [hident]
      linarith [hnoiseY i])
    (by
      intro h
      have hgap := real_interleaved_gap_budget N
        (fun i => p i (h.val + lag)) (fun i => c i (h.val + lag)) L
        (fun i hi => hpcle i hi (h.val + lag))
        (fun i hi => hcple i hi (h.val + lag))
        (hfirstPos h.val h.isLt) (hlastPos h.val h.isLt)
      have hident :
          (∑ i : Fin (N + 1),
            (c i.val (h.val + lag) - p i.val (h.val + lag))) =
          ∑ i ∈ Finset.range (N + 1),
            (c i (h.val + lag) - p i (h.val + lag)) := by
        exact Fin.sum_univ_eq_sum_range
          (fun i : ℕ => c i (h.val + lag) - p i (h.val + lag)) (N + 1)
      simp only [Finset.sum_add_distrib]
      rw [hident]
      linarith [hnoiseX h])

end OpenAI086
