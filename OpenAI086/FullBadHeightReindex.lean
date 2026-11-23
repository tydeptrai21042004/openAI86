import Mathlib
import OpenAI086.FullChronologicalBadDensity
import OpenAI086.FullChronologicalBadDensityStrict

/-!
# The exact initial-height split, Lemma 8.6

This file relates the `H+lag`-height counting statement to the
post-lag `H`-height argument without dropping the automatically bad
first `lag` heights.  Crucially, no assumption about the frequency of
bad events in the shorter window is introduced.
-/

namespace OpenAI086

/-- The original height index convention: the first `lag` tests are
identically one and the remaining ones are indexed after subtracting
`lag`.  The identity holds for arbitrary real-valued post-lag tests. -/
theorem full_bad_height_sum_split (H lag : ℕ) (f : ℕ → ℝ) :
    (∑ t : Fin (H + lag),
      if t.val < lag then (1 : ℝ) else f (t.val - lag)) =
      (lag : ℝ) + ∑ h : Fin H, f h.val := by
  rw [Fin.sum_univ_eq_sum_range]
  rw [show H + lag = lag + H by omega]
  rw [Finset.sum_range_add]
  have hfirst :
      (∑ t ∈ Finset.range lag,
        if t < lag then (1 : ℝ) else f (t - lag)) = (lag : ℝ) := by
    simp
  have hsecond :
      (∑ t ∈ Finset.range H,
        if lag + t < lag then (1 : ℝ) else f (lag + t - lag)) =
      ∑ h : Fin H, f h.val := by
    simp [Fin.sum_univ_eq_sum_range]
  rw [hfirst, hsecond]

/-- Faithful full-window predicate: the first `lag` heights count as
bad by definition, and subsequent heights use the manuscript's union
exception predicate with the correct shifted pair `(P_{h-lag},C_h)`. -/
noncomputable def fullPaperBadHeight
    {M N H lag : ℕ}
    (P C : ℕ → ℕ → Finset (Fin M))
    (X : Fin (N + 1) → Finset (Fin M))
    (Y : Fin (N + 1) → Fin H → Finset (Fin M))
    (beta : ℝ) (i : Fin (N + 1)) (t : Fin (H + lag)) : ℝ := by
  classical
  exact if ht : t.val < lag then 1 else
    paperUnionBadHeight integerLogBin11_10 (P i.val (t.val - lag))
      (C i.val t.val) (X i)
      (Y i ⟨t.val - lag, by omega⟩) beta

/-- No approximation: full bad-height sum is precisely the initial
segment plus the post-lag union tests. -/
theorem full_paper_bad_height_sum
    {M N H lag : ℕ}
    (P C : ℕ → ℕ → Finset (Fin M))
    (X : Fin (N + 1) → Finset (Fin M))
    (Y : Fin (N + 1) → Fin H → Finset (Fin M))
    (beta : ℝ) (i : Fin (N + 1)) :
    (∑ t : Fin (H + lag), fullPaperBadHeight P C X Y beta i t) =
      (lag : ℝ) +
        ∑ h : Fin H,
          paperUnionBadHeight integerLogBin11_10 (P i.val h.val)
            (C i.val (h.val + lag)) (X i) (Y i h) beta := by
  classical
  let f : ℕ → ℝ := fun h =>
    if ht : h < H then
      paperUnionBadHeight integerLogBin11_10 (P i.val h)
        (C i.val (h + lag)) (X i) (Y i ⟨h, ht⟩) beta
    else 0
  have hsplit := full_bad_height_sum_split H lag f
  convert hsplit using 1
  · apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < lag
    · simp [fullPaperBadHeight, ht]
    · have hidx : t.val - lag < H := by omega
      simp [fullPaperBadHeight, f, ht, hidx,
        Nat.sub_add_cancel (Nat.le_of_not_gt ht), Nat.add_comm]
  · apply congrArg (fun z : ℝ => (lag : ℝ) + z)
    apply Finset.sum_congr rfl
    intro h _
    simp [f, h.isLt, Nat.add_comm]

/-- The full paper-style lower density hypothesis implies the exact
`hfullBad` hypothesis of `full_chronological_integer_log_bad_density`.
This lemma exposes the reindexing explicitly, avoiding an unproved
post-lag density shortcut. -/
theorem full_bad_height_density_to_postlag
    {M N H lag : ℕ}
    (P C : ℕ → ℕ → Finset (Fin M))
    (X : Fin (N + 1) → Finset (Fin M))
    (Y : Fin (N + 1) → Fin H → Finset (Fin M))
    (beta delta : ℝ)
    (hbad : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) ≤
        ∑ t : Fin (H + lag), fullPaperBadHeight P C X Y beta i t) :
    ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) ≤ (lag : ℝ) +
        ∑ h : Fin H,
          paperUnionBadHeight integerLogBin11_10 (P i.val h.val)
            (C i.val (h.val + lag)) (X i) (Y i h) beta := by
  intro i
  simpa only [full_paper_bad_height_sum] using hbad i


/-- Complete full-window FINITE counting bridge with the exact original
paper-style bad-height sum, rather than a post-lag assumption.  The
result uses the endpoint inclusion repaired from the manuscript and
counts both horizontal and vertical exceptional labels via first-entry
rankings constructed from nested finite sets.

The quantitative hypotheses and the cardinality cap are explicit;
this is not a proof of any analytic step of the THT theorem. -/
theorem paper_full_chronological_integer_log_bad_density
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
    (hbadFull : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) ≤
        ∑ t : Fin (H + lag), fullPaperBadHeight P C X Y beta i t)
    (habsorb :
      2 * ((lag : ℝ) * ((integerLogBin11_10 M : ℕ) : ℝ) +
        (lag : ℝ) + A * finiteRankHarmonic M / beta) ≤
        delta * ((H + lag : ℕ) : ℝ)) :
    (((N + 1 : ℕ) : ℝ)) ≤
      2 * (((integerLogBin11_10 M : ℕ) : ℝ) +
        B * finiteRankHarmonic M / beta) / delta := by
  apply full_chronological_integer_log_bad_density
    N H lag M beta delta A B P C X Y
    hbeta hdelta hH hA hB hPheight hCheight hpc hcp
    hheightMultiplicity hpositionMultiplicity
  · exact full_bad_height_density_to_postlag P C X Y beta delta hbadFull
  · exact habsorb


/-- Complete full-window FINITE counting bridge with the exact original
paper-style bad-height sum, rather than a post-lag assumption.  The
result uses the endpoint inclusion repaired from the manuscript and
counts both horizontal and vertical exceptional labels via first-entry
rankings constructed from nested finite sets.

The quantitative hypotheses and the cardinality cap are explicit;
this is not a proof of any analytic step of the THT theorem. -/
theorem paper_full_chronological_integer_log_bad_density_strict
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
    (hbadFull : ∀ i : Fin (N + 1),
      delta * ((H + lag : ℕ) : ℝ) <
        ∑ t : Fin (H + lag), fullPaperBadHeight P C X Y beta i t)
    (habsorb :
      2 * ((lag : ℝ) * ((integerLogBin11_10 M : ℕ) : ℝ) +
        (lag : ℝ) + A * finiteRankHarmonic M / beta) ≤
        delta * ((H + lag : ℕ) : ℝ)) :
    (((N + 1 : ℕ) : ℝ)) <
      2 * (((integerLogBin11_10 M : ℕ) : ℝ) +
        B * finiteRankHarmonic M / beta) / delta := by
  apply full_chronological_integer_log_bad_density_strict
    N H lag M beta delta A B P C X Y
    hbeta hdelta hH hA hB hPheight hCheight hpc hcp
    hheightMultiplicity hpositionMultiplicity
  · exact full_bad_height_density_to_postlag P C X Y beta delta hbadFull
  · exact habsorb

end OpenAI086
