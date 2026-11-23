import Mathlib
import OpenAI086.FiniteChronologicalChain
import OpenAI086.ConcreteIntegerLogBadDensity

/-!
# Lemma 8.6: two-axis chain with chronological ranks CONSTRUCTED

The V12 version assumes rank-size inequalities for every exceptional
label. Here the two incidence estimates follow from the *finite nested
sets themselves*, using the unrestricted finite-chain harmonic lemma.
The two axes are ranked independently; neither assumes that original
Fin-label indices happen to be chronological ranks.

This is the shifted-window version of Lemma 8.6. It retains the paper's
bad-density and explicit numerical absorption assumptions, and does
not claim the general analytic proof of Theorem 1.1.
-/

namespace OpenAI086

/-- Interleaved inclusions imply monotonicity of the C-lists across
positions. Thus the horizontal rank order needs no new hypothesis. -/
theorem interleaved_C_position_mono {M N : ℕ}
    (P C : ℕ → ℕ → Finset (Fin M))
    (hpc : ∀ i ≤ N, ∀ h, P i h ⊆ C i h)
    (hcp : ∀ i < N, ∀ h, C i h ⊆ P (i + 1) h) :
    ∀ h, Monotone (fun i : Fin (N + 1) => C i.val h) := by
  intro h
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  change C i.val h ⊆ C (i.val + 1) h
  exact (hcp i.val i.isLt h).trans
    (hpc (i.val + 1) (by omega) h)

/-- Both incidence budgets are derived directly from per-label
multiplicity and nested finite sets, not from arbitrary entry rankings.
Horizontal monotonicity of C is itself derived from `hpc` and `hcp`;
no independent first-entry order or position-monotonicity hypothesis is used. -/
theorem concrete_chronological_integer_log_chain
    (N H lag M : ℕ) (beta delta A B : ℝ)
    (P C : ℕ → ℕ → Finset (Fin M))
    (X : Fin (N + 1) → Finset (Fin M))
    (Y : Fin (N + 1) → Fin H → Finset (Fin M))
    (hbeta : 0 < beta) (hdelta : 0 < delta) (hH : 0 < H)
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
  exact concrete_integer_log_bad_density_chain
    N H lag M beta delta
    (A * finiteRankHarmonic M) (B * finiteRankHarmonic M)
    P C X Y hbeta hdelta hH hPheight hpc hcp
    (by intro i hi h; simpa using (Finset.card_le_univ (C i h)))
    hY hX hbad hbudget

end OpenAI086
