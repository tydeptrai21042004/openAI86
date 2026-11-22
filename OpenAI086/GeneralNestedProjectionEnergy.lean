import Mathlib

/-!
# Lemma 3.3: square variation of a single nested projection family

This is the **general finite-dimensional real Hilbert-space m = 1 case**
of the second conclusion of Lemma 3.3.  The projections are arbitrary
self-adjoint idempotent maps with nested ranges, *not just coordinate masks*.
The proof derives orthogonality of successive increments from the projection
axioms and then telescopes their exact squared energies.  Its constant is 1
for every number of depth generations.

The paper's m > 1 noncommuting products and its arbitrary-row logarithmic
inequality are not proved here.  The use of real finite-dimensional space is
also explicit; extending to complex arbitrary Hilbert spaces remains open.
-/

namespace OpenAI086

/-- The ordinary Euclidean pairing, without an inner-product API dependency. -/
def finiteRealPair {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, u i * v i

private theorem finiteRealPair_comm {n : ℕ} (u v : Fin n → ℝ) :
    finiteRealPair u v = finiteRealPair v u := by
  unfold finiteRealPair
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem finiteRealPair_self_nonneg {n : ℕ} (u : Fin n → ℝ) :
    0 ≤ finiteRealPair u u := by
  unfold finiteRealPair
  apply Finset.sum_nonneg
  intro i _
  nlinarith [sq_nonneg (u i)]

private theorem finiteRealPair_sub_self {n : ℕ} (u v : Fin n → ℝ) :
    finiteRealPair (u - v) (u - v) =
      finiteRealPair u u + finiteRealPair v v - 2 * finiteRealPair u v := by
  unfold finiteRealPair
  change (∑ i : Fin n, (u i - v i) * (u i - v i)) =
    (∑ i : Fin n, u i * u i) + (∑ i : Fin n, v i * v i) -
      2 * (∑ i : Fin n, u i * v i)
  calc
    (∑ i : Fin n, (u i - v i) * (u i - v i)) =
        ∑ i : Fin n, (u i * u i + v i * v i - 2 * (u i * v i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = _ := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]

/-- Self-adjoint, idempotent maps retain exactly their own squared norm
when paired against the original input. -/
theorem nested_projection_pair_identity {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v, finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (k : ℕ) (x : Fin n → ℝ) :
    finiteRealPair (P k x) (P k x) = finiteRealPair x (P k x) := by
  calc
    finiteRealPair (P k x) (P k x) =
        finiteRealPair x (P k (P k x)) := hsym k x (P k x)
    _ = finiteRealPair x (P k x) := by rw [hidemp k x]

/-- One projection cannot increase the squared Euclidean norm. -/
theorem nested_projection_single_energy {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v, finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (k : ℕ) (x : Fin n → ℝ) :
    finiteRealPair (P k x) (P k x) ≤ finiteRealPair x x := by
  have hnonneg := finiteRealPair_self_nonneg (x - P k x)
  rw [finiteRealPair_sub_self] at hnonneg
  rw [← nested_projection_pair_identity P hsym hidemp k x] at hnonneg
  linarith

/-- Orthogonality of an increment to the preceding projection, expressed
as a Pythagorean identity.  Only **within-family** nesting is required. -/
theorem nested_projection_increment_identity {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v, finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (k : ℕ) (x : Fin n → ℝ) :
    finiteRealPair (P (k + 1) x - P k x)
        (P (k + 1) x - P k x) =
      finiteRealPair (P (k + 1) x) (P (k + 1) x) -
        finiteRealPair (P k x) (P k x) := by
  have hcross :
      finiteRealPair (P (k + 1) x) (P k x) =
        finiteRealPair (P k x) (P k x) := by
    calc
      finiteRealPair (P (k + 1) x) (P k x) =
          finiteRealPair (P k x) (P (k + 1) x) := finiteRealPair_comm _ _
      _ = finiteRealPair x (P k (P (k + 1) x)) := hsym k x (P (k + 1) x)
      _ = finiteRealPair x (P k x) := by rw [hnested k x]
      _ = finiteRealPair (P k x) (P k x) :=
          (nested_projection_pair_identity P hsym hidemp k x).symm
  rw [finiteRealPair_sub_self, hcross]
  ring

/-- Exact telescoping squared-energy identity for nested projections.
This is the quantitative m=1 step for arbitrary real orthogonal projections. -/
theorem nested_projection_square_variation_exact {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v, finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (x : Fin n → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        finiteRealPair (P (k + 1) x - P k x)
          (P (k + 1) x - P k x)) =
      finiteRealPair (P N x) (P N x) - finiteRealPair (P 0 x) (P 0 x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [nested_projection_increment_identity P hsym hidemp hnested N x]
      ring

/-- Uniform depth-free Bessel bound, with the sharp constant one.
This proves the second estimate of the paper's Lemma 3.3 for m=1
in a finite real Hilbert-space model. -/
theorem nested_projection_square_variation_bound {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v, finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (x : Fin n → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      finiteRealPair (P (k + 1) x - P k x)
        (P (k + 1) x - P k x)) ≤ finiteRealPair x x := by
  rw [nested_projection_square_variation_exact P hsym hidemp hnested x N]
  have htop := nested_projection_single_energy P hsym hidemp N x
  have hbase := finiteRealPair_self_nonneg (P 0 x)
  linarith

end OpenAI086
