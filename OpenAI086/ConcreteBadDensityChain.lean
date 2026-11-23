import Mathlib
import OpenAI086.PaperBadHeightPredicate
import OpenAI086.HeightPositionChainBridge

/-!
# Lemma 8.6: finite sets -> two-axis density chain bound

This theorem REPLACES V10's assumed pointwise `hpoint` by the actual
union-based bad-height predicate on changing finite label sets, and
DERIVES all logarithmic rank monotonicity and endpoint budgets from
inclusions.  The endpoint `P_N,h ⊆ C_N,h` is explicitly required.

What is still assumed: the two independent exceptional-incidence
bounds (the Lemma 8.5 step) and the density of bad heights. Thus this
is a precise, set-based counting bridge, not an unqualified proof of
manuscript Lemma 8.6 or of the main trilinear theorem.

Here `H` indexes tested heights h=0,...,H-1 and the second set in the
rank test lies at height `h+lag` (paper's post-lag convention).
-/

namespace OpenAI086

/-- The outer (row-wise) count from nested label sets. The conclusion
has NO unproved abstract pointwise indicator or rank inequality.
The remaining exceptional incidence bounds are explicit, in terms of
real cardinal fractions of the actual finite sets. -/
theorem concrete_union_bad_density_chain
    {α : Type*} [DecidableEq α]
    (N H lag : ℕ) (beta delta L A B : ℝ)
    (rank : ℕ → ℕ) (hrank : Monotone rank)
    (P C : ℕ → ℕ → Finset α)
    (X : Fin (N + 1) → Finset α)
    (Y : Fin (N + 1) → Fin H → Finset α)
    (hbeta : 0 < beta) (hdelta : 0 < delta) (hH : 0 < H)
    (hheight : ∀ i ≤ N, Monotone (P i))
    (hpc : ∀ i ≤ N, ∀ h, P i h ⊆ C i h)
    (hcp : ∀ i < N, ∀ h, C i h ⊆ P (i + 1) h)
    (hcap : ∀ i ≤ N, ∀ h, ((rank (C i h).card : ℕ) : ℝ) ≤ L)
    (hY : ∀ i : Fin (N + 1),
      (∑ h : Fin H,
        (((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
         ((C i.val (h.val + lag)).card : ℝ))) ≤ A)
    (hX : ∀ h : Fin H,
      (∑ i : Fin (N + 1),
        (((X i ∩ C i.val (h.val + lag)).card : ℝ) /
         ((C i.val (h.val + lag)).card : ℝ))) ≤ B)
    (hbad : ∀ i : Fin (N + 1),
      delta * (H : ℝ) ≤
        ∑ h : Fin H,
          paperUnionBadHeight rank (P i.val h.val)
            (C i.val (h.val + lag)) (X i) (Y i h) beta)
    (hbudget : 2 * ((lag : ℝ) * L + A / beta) ≤ delta * (H : ℝ)) :
    ((N + 1 : ℕ) : ℝ) ≤ 2 * (L + B / beta) / delta := by
  classical
  let p : ℕ → ℕ → ℝ := fun i h => (rank (P i h).card : ℝ)
  let c : ℕ → ℕ → ℝ := fun i h => (rank (C i h).card : ℝ)
  let noiseY : Fin (N + 1) → Fin H → ℝ := fun i h =>
    ((((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
      ((C i.val (h.val + lag)).card : ℝ)) / beta)
  let noiseX : Fin (N + 1) → Fin H → ℝ := fun i h =>
    ((((X i ∩ C i.val (h.val + lag)).card : ℝ) /
      ((C i.val (h.val + lag)).card : ℝ)) / beta)
  let bad : Fin (N + 1) → Fin H → ℝ := fun i h =>
    paperUnionBadHeight rank (P i.val h.val)
      (C i.val (h.val + lag)) (X i) (Y i h) beta
  have hpcle : ∀ i ≤ N, ∀ h, p i h ≤ c i h := by
    intro i hi h
    dsimp [p, c]
    exact_mod_cast finite_set_rank_monotone rank hrank
      (P i h) (C i h) (hpc i hi h)
  have hcple : ∀ i < N, ∀ h, c i h ≤ p (i + 1) h := by
    intro i hi h
    dsimp [p, c]
    exact_mod_cast finite_set_rank_monotone rank hrank
      (C i h) (P (i + 1) h) (hcp i hi h)
  have hfirstH : ∀ i ≤ N, ∀ r < lag, 0 ≤ p i r := by
    intro i _ r _
    dsimp [p]
    positivity
  have hlastH : ∀ i ≤ N, ∀ r < lag, p i (H + r) ≤ L := by
    intro i hi r _
    exact (hpcle i hi (H + r)).trans (hcap i hi (H + r))
  have hfirstPos : ∀ h < H, 0 ≤ p 0 (h + lag) := by
    intro h _
    dsimp [p]
    positivity
  have hlastPos : ∀ h < H, c N (h + lag) ≤ L := by
    intro h _
    exact hcap N (le_refl N) (h + lag)
  have hnoiseY : ∀ i : Fin (N + 1),
      (∑ h : Fin H, noiseY i h) ≤ A / beta := by
    intro i
    change (∑ h : Fin H,
      ((((Y i h ∩ C i.val (h.val + lag)).card : ℝ) /
        ((C i.val (h.val + lag)).card : ℝ)) / beta)) ≤ A / beta
    rw [Finset.sum_div]
    exact div_le_div_of_nonneg_right (hY i) (le_of_lt hbeta)
  have hnoiseX : ∀ h : Fin H,
      (∑ i : Fin (N + 1), noiseX i h) ≤ B / beta := by
    intro h
    change (∑ i : Fin (N + 1),
      ((((X i ∩ C i.val (h.val + lag)).card : ℝ) /
        ((C i.val (h.val + lag)).card : ℝ)) / beta)) ≤ B / beta
    rw [Finset.sum_div]
    exact div_le_div_of_nonneg_right (hX h) (le_of_lt hbeta)
  have hpoint : ∀ i : Fin (N + 1), ∀ h : Fin H,
      bad i h ≤
        ((p i.val (h.val + lag) - p i.val h.val) + noiseY i h) +
        ((c i.val (h.val + lag) - p i.val (h.val + lag)) +
          noiseX i h) := by
    intro i h
    have hmono : P i.val h.val ⊆ P i.val (h.val + lag) :=
      (hheight i.val (by omega)) (Nat.le_add_right h.val lag)
    have hmain := paper_union_bad_height_pointwise rank hrank
      (P i.val h.val) (P i.val (h.val + lag))
      (C i.val (h.val + lag)) (X i) (Y i h)
      hmono (hpc i.val (by omega) (h.val + lag)) beta hbeta
    dsimp [bad, p, c, noiseY, noiseX]
    rw [add_div] at hmain
    linarith
  have hbad' : ∀ i : Fin (N + 1),
      delta * (H : ℝ) ≤ ∑ h : Fin H, bad i h := hbad
  exact bad_density_chain_with_both_telescopes
    N H lag delta L (A / beta) (B / beta)
    p c noiseY noiseX bad hdelta hH hpcle hcple
    hfirstH hlastH hfirstPos hlastPos
    hnoiseY hnoiseX hpoint hbad' hbudget

end OpenAI086
