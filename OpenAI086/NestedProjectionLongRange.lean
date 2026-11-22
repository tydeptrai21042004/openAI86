import Mathlib
import OpenAI086.GeneralNestedProjectionEnergy

/-!
# Lemma 3.3: long-range nesting and separated increments

The previous file proved one-step Pythagoras and the sharp m=1 square
variation.  Here nesting is propagated to arbitrary generations, and
increments at *nonoverlapping* generations are proved orthogonal.
This uses only self-adjointness, idempotence, and order of the nesting;
it does **not** assume that unrelated projection families commute.

The full arbitrary-row logarithmic inequality of Lemma 3.3 and its
multi-family m>1 product estimate remain separate obligations.
-/

namespace OpenAI086

/-- The nesting relation propagates through any number of generations.
Linear structure is not needed for the composition identity. -/
theorem nested_projection_at_lag {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (i d : ℕ) (x : Fin n → ℝ) :
    P i (P (i + d) x) = P i x := by
  induction d generalizing x with
  | zero => simpa using hidemp i x
  | succ d ih =>
      have hstep :
          P (i + d) (P (i + (d + 1)) x) = P (i + d) x := by
        simpa only [Nat.add_succ] using hnested (i + d) x
      calc
        P i (P (i + (d + 1)) x) =
            P i (P (i + d) (P (i + (d + 1)) x)) := by
              simpa only [Nat.add_succ] using
                (ih (P (i + (d + 1)) x)).symm
        _ = P i (P (i + d) x) := by
              rw [hstep]
        _ = P i x := ih x

/-- Every earlier projection absorbs every later projection. -/
theorem nested_projection_at_le {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (i j : ℕ) (hij : i ≤ j) (x : Fin n → ℝ) :
    P i (P j x) = P i x := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
  rw [hd]
  exact nested_projection_at_lag P hidemp hnested i d x

/-- The mixed inner product of two nested projection outputs is exactly
the squared norm of the earlier output. -/
theorem nested_projection_cross_energy {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (i j : ℕ) (hij : i ≤ j) (x : Fin n → ℝ) :
    finiteRealPair (P i x) (P j x) =
      finiteRealPair (P i x) (P i x) := by
  calc
    finiteRealPair (P i x) (P j x) =
        finiteRealPair x (P i (P j x)) := hsym i x (P j x)
    _ = finiteRealPair x (P i x) := by
          rw [nested_projection_at_le P hidemp hnested i j hij x]
    _ = finiteRealPair (P i x) (P i x) :=
          (nested_projection_pair_identity P hsym hidemp i x).symm

/-- Non-adjacent projection increments are orthogonal.  This is the
Bessel orthogonality used when grouping dyadic blocks of one family. -/
theorem nested_projection_disjoint_increments {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (k l : ℕ) (hkl : k + 1 ≤ l) (x : Fin n → ℝ) :
    finiteRealPair (P (k + 1) x - P k x)
      (P (l + 1) x - P l x) = 0 := by
  have hk_l : k ≤ l := (Nat.le_succ k).trans hkl
  have hk_lp : k ≤ l + 1 := hk_l.trans (Nat.le_succ l)
  have hkp_lp : k + 1 ≤ l + 1 := hkl.trans (Nat.le_succ l)
  have h₁ := nested_projection_cross_energy P hsym hidemp hnested
    (k + 1) (l + 1) hkp_lp x
  have h₂ := nested_projection_cross_energy P hsym hidemp hnested
    (k + 1) l hkl x
  have h₃ := nested_projection_cross_energy P hsym hidemp hnested
    k (l + 1) hk_lp x
  have h₄ := nested_projection_cross_energy P hsym hidemp hnested
    k l hk_l x
  have hexpand :
      finiteRealPair (P (k + 1) x - P k x)
          (P (l + 1) x - P l x) =
        finiteRealPair (P (k + 1) x) (P (l + 1) x) -
        finiteRealPair (P (k + 1) x) (P l x) -
        finiteRealPair (P k x) (P (l + 1) x) +
        finiteRealPair (P k x) (P l x) := by
    unfold finiteRealPair
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hexpand, h₁, h₂, h₃, h₄]
  ring

/-- Exact square-energy of the increments in an arbitrary window.
The result is independent of the starting scale and the window length. -/
theorem nested_projection_window_energy_exact {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (i count : ℕ) (x : Fin n → ℝ) :
    (∑ t ∈ Finset.range count,
        finiteRealPair (P (i + t + 1) x - P (i + t) x)
          (P (i + t + 1) x - P (i + t) x)) =
      finiteRealPair (P (i + count) x) (P (i + count) x) -
        finiteRealPair (P i x) (P i x) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := nested_projection_increment_identity P hsym hidemp hnested
        (i + count) x
      simp only [Nat.add_succ]
      rw [hstep]
      ring

/-- Sharp depth-free energy bound for an arbitrary subinterval of
increments (the finite real m=1 case of Lemma 3.3). -/
theorem nested_projection_window_energy_bound {n : ℕ}
    (P : ℕ → (Fin n → ℝ) → (Fin n → ℝ))
    (hsym : ∀ k u v,
      finiteRealPair (P k u) v = finiteRealPair u (P k v))
    (hidemp : ∀ k u, P k (P k u) = P k u)
    (hnested : ∀ k u, P k (P (k + 1) u) = P k u)
    (i count : ℕ) (x : Fin n → ℝ) :
    (∑ t ∈ Finset.range count,
        finiteRealPair (P (i + t + 1) x - P (i + t) x)
          (P (i + t + 1) x - P (i + t) x)) ≤
      finiteRealPair x x := by
  rw [nested_projection_window_energy_exact P hsym hidemp hnested i count x]
  have htop := nested_projection_single_energy P hsym hidemp (i + count) x
  have hbottom : 0 ≤ finiteRealPair (P i x) (P i x) := by
    unfold finiteRealPair
    apply Finset.sum_nonneg
    intro j _
    nlinarith [sq_nonneg (P i x j)]
  linarith

end OpenAI086
