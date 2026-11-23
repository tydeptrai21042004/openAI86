import Mathlib
import OpenAI086.IntegerLogExact
import OpenAI086.ConcreteBadDensityChain

/-!
# Lemma 8.6: specialize the set-based chain to the actual 1.1 binning

Unlike `ConcreteBadDensityChain`, this statement has no arbitrary
`rank` argument or monotonicity hypothesis for that argument. The
rank is the integer-arithmetic threshold count `integerLogBin11_10`,
with its complete finite search window established in
`IntegerLogExact.lean`.

The exceptional fractions and their aggregate bounds remain explicit
hypotheses. This is a specialization of the counting bridge, not an
independent completion of manuscript Lemma 8.6.
-/

namespace OpenAI086

/-- Full finite-set chain using a concrete integer implementation of
the paper's base-1.1 floor-log cardinality bins. `hcap` is the exact
paper-style bound on the *cardinality*, rather than a postulated rank
bound. The endpoint inclusion at the last position is explicit. -/
theorem concrete_integer_log_bad_density_chain
    {α : Type*} [DecidableEq α]
    (N H lag M : ℕ) (beta delta A B : ℝ)
    (P C : ℕ → ℕ → Finset α)
    (X : Fin (N + 1) → Finset α)
    (Y : Fin (N + 1) → Fin H → Finset α)
    (hbeta : 0 < beta) (hdelta : 0 < delta) (hH : 0 < H)
    (hheight : ∀ i ≤ N, Monotone (P i))
    (hpc : ∀ i ≤ N, ∀ h, P i h ⊆ C i h)
    (hcp : ∀ i < N, ∀ h, C i h ⊆ P (i + 1) h)
    (hcap : ∀ i ≤ N, ∀ h, (C i h).card ≤ M)
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
          paperUnionBadHeight integerLogBin11_10 (P i.val h.val)
            (C i.val (h.val + lag)) (X i) (Y i h) beta)
    (hbudget :
      2 * ((lag : ℝ) * (integerLogBin11_10 M : ℝ) + A / beta) ≤
        delta * (H : ℝ)) :
    ((N + 1 : ℕ) : ℝ) ≤
      2 * ((integerLogBin11_10 M : ℝ) + B / beta) / delta := by
  classical
  apply concrete_union_bad_density_chain
    N H lag beta delta (integerLogBin11_10 M : ℝ) A B
    integerLogBin11_10 integer_log_bin_11_10_monotone
    P C X Y hbeta hdelta hH hheight hpc hcp
  · intro i hi h
    exact_mod_cast integer_log_bin_card_le (C i h) M (hcap i hi h)
  · exact hY
  · exact hX
  · exact hbad
  · exact hbudget

end OpenAI086
