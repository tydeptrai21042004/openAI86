import Mathlib
import OpenAI086.FiniteAlignedProjectionBlocks

/-!
# Arbitrary-length consecutive projection blocks: a dyadic-prefix bridge

A binary-prefix partition uses intervals of DIFFERENT lengths. The
fixed-length aligned-block lemma alone does not capture this. Here we
allow arbitrary monotone cut points, prove exact telescoping of squared
energies and retain the sharp one-constant Bessel bound. No integer
power-of-two or divisibility hypothesis appears, so the theorem applies
to *any* actual dyadic prefix partition once its boundaries are built.

The proof is finite-dimensional real. Producing row-adaptive binary
prefix partitions, the logarithmic row estimate and the many-family
product estimate of Lemma 3.3 are still open.
-/

namespace OpenAI086

/-- Projection increment across the k-th interval in an arbitrary
monotone list of cuts. -/
def variableProjectionBlock {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (cut : ℕ → ℕ) (k : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  P (cut (k + 1)) x - P (cut k) x

/-- Exact Pythagorean energy for a finite sequence of monotone cuts.
The cuts can have unequal gaps or repeated values. -/
theorem variable_projection_block_energy_exact {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (cut : ℕ → ℕ) (hcut : ∀ k, cut k ≤ cut (k + 1))
    (count : ℕ) (x : Fin n → ℝ) :
    (∑ k ∈ Finset.range count,
      finiteRealPair (variableProjectionBlock P cut k x)
        (variableProjectionBlock P cut k x)) =
      finiteRealPair (P (cut count) x) (P (cut count) x) -
      finiteRealPair (P (cut 0) x) (P (cut 0) x) := by
  induction count with
  | zero => simp [variableProjectionBlock]
  | succ count ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := nested_projection_distant_increment_identity
        P hsym hidemp hnested (cut count) (cut (count + 1))
        (hcut count) x
      change finiteRealPair (variableProjectionBlock P cut count x)
          (variableProjectionBlock P cut count x) =
        finiteRealPair (P (cut (count + 1)) x)
          (P (cut (count + 1)) x) -
        finiteRealPair (P (cut count) x)
          (P (cut count) x) at hstep
      rw [hstep]
      ring

/-- Uniform Bessel bound for arbitrary interval lengths. Unlike a
cardinality bound, its constant is one regardless of the number of
cuts or the largest cut point. -/
theorem variable_projection_block_energy_bound {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (cut : ℕ → ℕ) (hcut : ∀ k, cut k ≤ cut (k + 1))
    (count : ℕ) (x : Fin n → ℝ) :
    (∑ k ∈ Finset.range count,
      finiteRealPair (variableProjectionBlock P cut k x)
        (variableProjectionBlock P cut k x)) ≤
      finiteRealPair x x := by
  rw [variable_projection_block_energy_exact P hsym hidemp hnested
    cut hcut count x]
  have htop := nested_projection_single_energy P hsym hidemp
    (cut count) x
  have hbottom : 0 ≤ finiteRealPair (P (cut 0) x) (P (cut 0) x) := by
    unfold finiteRealPair
    apply Finset.sum_nonneg
    intro k _
    nlinarith [sq_nonneg (P (cut 0) x k)]
  linarith

end OpenAI086
