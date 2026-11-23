import Mathlib
import OpenAI086.IntegerLogBins

/-!
# Exact base-11/10 cardinality bins, without floating-point logarithms

Lemma 8.6 compares floor-logarithmic cardinalities in base 1.1. V11
counted the integer thresholds 11^(k+1) ≤ n * 10^(k+1), but had
not established that its finite search window included all possible
thresholds. This module PROVES that finite-window assertion.

The bound is intentionally very loose: 10(n+1) integer trials. It is
sufficient for correctness of a finite executable definition. This is
still only the counting rank used within Lemma 8.6; it does not prove
the manuscript's entire lemma or its application to the trilinear
operator. No real floating-point computation is used.
-/

namespace OpenAI086

/-- Integer Bernoulli inequality: (1+1/10)^k ≥ 1+k/10.
Written with integer powers, so no analytic approximation is involved. -/
theorem eleven_tenths_bernoulli (k : ℕ) :
    (k + 10) * 10 ^ k ≤ 10 * 11 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hc : 10 * (k + 11) ≤ 11 * (k + 10) := by omega
      calc
        (k + 1 + 10) * 10 ^ (k + 1) =
            (10 * (k + 11)) * 10 ^ k := by
              simp only [pow_succ]
              ring
        _ ≤ (11 * (k + 10)) * 10 ^ k :=
            Nat.mul_le_mul_right (10 ^ k) hc
        _ = 11 * ((k + 10) * 10 ^ k) := by ring
        _ ≤ 11 * (10 * 11 ^ k) := Nat.mul_le_mul_left 11 ih
        _ = 10 * 11 ^ (k + 1) := by
            simp only [pow_succ]
            ring

/-- Any integer exponent passing the 1.1 logarithmic threshold lies
strictly inside the V11 search window. This is the missing completeness
argument for `integerLogBin11_10`. -/
theorem eleven_tenths_threshold_in_window (n k : ℕ)
    (hthreshold : 11 ^ (k + 1) ≤ n * 10 ^ (k + 1)) :
    k < 10 * (n + 1) := by
  by_contra hnot
  have hk : 10 * (n + 1) ≤ k := by omega
  have hcoeff : 10 * n < k + 11 := by omega
  have hpow : 0 < 10 ^ (k + 1) := by positivity
  have hstrict :
      (10 * n) * 10 ^ (k + 1) < (k + 11) * 10 ^ (k + 1) :=
    Nat.mul_lt_mul_of_pos_right hcoeff hpow
  have hbern : (k + 11) * 10 ^ (k + 1) ≤
      10 * 11 ^ (k + 1) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (eleven_tenths_bernoulli (k + 1))
  have hupper : 10 * 11 ^ (k + 1) ≤
      (10 * n) * 10 ^ (k + 1) := by
    calc
      10 * 11 ^ (k + 1) ≤ 10 * (n * 10 ^ (k + 1)) :=
        Nat.mul_le_mul_left 10 hthreshold
      _ = (10 * n) * 10 ^ (k + 1) := by ring
  exact (not_le_of_gt hstrict) (hbern.trans hupper)

/-- Enlarging the filter window beyond 10(n+1) cannot add further
base-1.1 thresholds. This certifies that V11's rank is independent
of the chosen sufficiently large finite search window. -/
theorem integer_log_11_10_window_stable (n K : ℕ)
    (hK : 10 * (n + 1) ≤ K) :
    ((Finset.range K).filter
      (fun k : ℕ => 11 ^ (k + 1) ≤ n * 10 ^ (k + 1))).card =
      integerLogBin11_10 n := by
  classical
  have hset :
      (Finset.range K).filter
        (fun k : ℕ => 11 ^ (k + 1) ≤ n * 10 ^ (k + 1)) =
      (Finset.range (10 * (n + 1))).filter
        (fun k : ℕ => 11 ^ (k + 1) ≤ n * 10 ^ (k + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨eleven_tenths_threshold_in_window n k h.2, h.2⟩
    · intro h
      exact ⟨lt_of_lt_of_le h.1 hK, h.2⟩
  exact (congrArg Finset.card hset).trans rfl

/-- Every successful threshold is also successful at the preceding
exponent. Thus the successful exponent set is an initial segment,
not an arbitrary collection of thresholds. -/
theorem eleven_tenths_threshold_down (n k : ℕ)
    (h : 11 ^ (k + 2) ≤ n * 10 ^ (k + 2)) :
    11 ^ (k + 1) ≤ n * 10 ^ (k + 1) := by
  have hstep :
      11 * 11 ^ (k + 1) ≤ 10 * (n * 10 ^ (k + 1)) := by
    simpa [pow_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hsmall : 10 * 11 ^ (k + 1) ≤ 11 * 11 ^ (k + 1) :=
    Nat.mul_le_mul_right _ (by norm_num : 10 ≤ 11)
  omega

/-- A downward-closed exact exponent condition, required for matching
the threshold count to the genuine integer floor-logarithm. -/
theorem eleven_tenths_threshold_antitone (n : ℕ) :
    ∀ j k : ℕ, k ≤ j →
      11 ^ (j + 1) ≤ n * 10 ^ (j + 1) →
      11 ^ (k + 1) ≤ n * 10 ^ (k + 1) := by
  intro j
  induction j with
  | zero =>
      intro k hkj hj
      have hk : k = 0 := by omega
      subst k
      exact hj
  | succ j ih =>
      intro k hkj hj
      by_cases hk : k = j + 1
      · subst k
        exact hj
      · have hk' : k ≤ j := by omega
        apply ih k hk'
        apply eleven_tenths_threshold_down n j
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

/-- The exact finite integer rank always lies within its certified
search interval. In particular, it is a well-defined nonnegative
bounded cardinality rank without any real logarithm implementation. -/
theorem integer_log_bin_11_10_bounded (n : ℕ) :
    integerLogBin11_10 n ≤ 10 * (n + 1) := by
  unfold integerLogBin11_10
  exact (Finset.card_filter_le _ _).trans (by simp)

end OpenAI086
