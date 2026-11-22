import Mathlib
import OpenAI086.NestedProjectionLongRange

/-!
# Aligned blocks of arbitrary nested orthogonal projections (Lemma 3.3)

For a *single* nested family of self-adjoint idempotent maps, the
energy of every collection of aligned, disjoint contiguous projection
increments is bounded by the input energy with sharp constant one.
The blocks need not be rank-one, coordinate projections, or of length
one; the bound is independent of both the number and length of blocks.

This constructs an actual fixed-length block-energy estimate needed by
the Rademacher--Menshov argument, rather than postulating Bessel
energy for abstract block signals. It does NOT yet construct each
row-selected dyadic prefix or the full many-family logarithmic estimate.
-/

namespace OpenAI086

/-- Squared variation between any two comparable projections, not
necessarily successive generations. -/
theorem nested_projection_distant_increment_identity {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (i j : ℕ) (hij : i ≤ j) (x : Fin n → ℝ) :
    finiteRealPair (P j x - P i x) (P j x - P i x) =
      finiteRealPair (P j x) (P j x) -
        finiteRealPair (P i x) (P i x) := by
  have hcross := nested_projection_cross_energy P hsym hidemp hnested
    i j hij x
  have hcomm : finiteRealPair (P j x) (P i x) =
      finiteRealPair (P i x) (P j x) := by
    unfold finiteRealPair
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hexpand :
      finiteRealPair (P j x - P i x) (P j x - P i x) =
        finiteRealPair (P j x) (P j x) -
        finiteRealPair (P j x) (P i x) -
        finiteRealPair (P i x) (P j x) +
        finiteRealPair (P i x) (P i x) := by
    unfold finiteRealPair
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hexpand, hcomm, hcross]
  ring

/-- An aligned block can have any integer length, including zero. -/
def alignedProjectionBlock {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (start step k : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  P (start + (k + 1) * step) x - P (start + k * step) x

/-- Pythagorean telescoping of actual aligned block increments. -/
theorem aligned_projection_block_energy_exact {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (start step count : ℕ) (x : Fin n → ℝ) :
    (∑ k ∈ Finset.range count,
      finiteRealPair (alignedProjectionBlock P start step k x)
        (alignedProjectionBlock P start step k x)) =
      finiteRealPair (P (start + count * step) x)
        (P (start + count * step) x) -
      finiteRealPair (P start x) (P start x) := by
  induction count with
  | zero => simp [alignedProjectionBlock]
  | succ count ih =>
      rw [Finset.sum_range_succ, ih]
      have hle : start + count * step ≤
          start + (count + 1) * step :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_right step (Nat.le_succ count)) start
      have hstep := nested_projection_distant_increment_identity
        P hsym hidemp hnested
        (start + count * step) (start + (count + 1) * step)
        hle x
      change finiteRealPair (alignedProjectionBlock P start step count x)
          (alignedProjectionBlock P start step count x) =
        finiteRealPair (P (start + (count + 1) * step) x)
          (P (start + (count + 1) * step) x) -
        finiteRealPair (P (start + count * step) x)
          (P (start + count * step) x) at hstep
      rw [hstep]
      ring

/-- Uniform bound with no cost from the number or the length of the
blocks. It is a Bessel inequality for a genuine nested projection
family, not an assumption about arbitrarily assigned vectors. -/
theorem aligned_projection_block_energy_bound {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (start step count : ℕ) (x : Fin n → ℝ) :
    (∑ k ∈ Finset.range count,
      finiteRealPair (alignedProjectionBlock P start step k x)
        (alignedProjectionBlock P start step k x)) ≤
      finiteRealPair x x := by
  rw [aligned_projection_block_energy_exact P hsym hidemp hnested
    start step count x]
  have htop := nested_projection_single_energy P hsym hidemp
    (start + count * step) x
  have hbase : 0 ≤ finiteRealPair (P start x) (P start x) := by
    unfold finiteRealPair
    apply Finset.sum_nonneg
    intro k _
    nlinarith [sq_nonneg (P start x k)]
  linarith

/-- Any two disjoint *interval* projection increments are orthogonal,
even if their lengths are different. This is the form needed for dyadic
blocks of different lengths in the binary-prefix decomposition. -/
theorem nested_projection_disjoint_blocks_orthogonal {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (a b c d : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (x : Fin n → ℝ) :
    finiteRealPair (P b x - P a x) (P d x - P c x) = 0 := by
  have hbd := nested_projection_cross_energy P hsym hidemp hnested
    b d (hbc.trans hcd) x
  have hbc' := nested_projection_cross_energy P hsym hidemp hnested
    b c hbc x
  have had := nested_projection_cross_energy P hsym hidemp hnested
    a d ((hab.trans hbc).trans hcd) x
  have hac := nested_projection_cross_energy P hsym hidemp hnested
    a c (hab.trans hbc) x
  have hexpand :
      finiteRealPair (P b x - P a x) (P d x - P c x) =
        finiteRealPair (P b x) (P d x) -
        finiteRealPair (P b x) (P c x) -
        finiteRealPair (P a x) (P d x) +
        finiteRealPair (P a x) (P c x) := by
    unfold finiteRealPair
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hexpand, hbd, hbc', had, hac]
  ring

end OpenAI086
