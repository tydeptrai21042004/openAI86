import Mathlib
import OpenAI086.FiniteReductions

/-!
# A finite-dimensional, independently proved special case of the
# nested projection energy mechanism in OpenAI #086, Section 3.3

Coordinate masks are **commuting** orthogonal projections.  The difficult
Lemma 3.3 in the paper allows products of multiple NONCOMMUTING projection
families and arbitrary Bessel rows.  This file does not prove that lemma.
-/

namespace OpenAI086

/-- Coordinate projection onto a finite collection of coordinates. -/
def coordMask {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ S then x i else 0

/-- Squared Euclidean norm of a finite coordinate vector. -/
def coordEnergy {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (x i) ^ 2

/-- A coordinate mask is an idempotent projection. -/
theorem coordMask_idempotent {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    coordMask S (coordMask S x) = coordMask S x := by
  funext i
  by_cases hi : i ∈ S <;> simp [coordMask, hi]

/-- If `S ⊆ T`, then applying the larger mask before the smaller changes nothing. -/
theorem coordMask_nested {n : ℕ}
    (S T : Finset (Fin n)) (x : Fin n → ℝ) (h : S ⊆ T) :
    coordMask S (coordMask T x) = coordMask S x := by
  funext i
  by_cases hi : i ∈ S
  · have ht : i ∈ T := h hi
    simp [coordMask, hi, ht]
  · simp [coordMask, hi]

/-- Orthogonal coordinate projections are L² contractions. -/
theorem coordMask_energy_le {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → ℝ) :
    coordEnergy (coordMask S x) ≤ coordEnergy x := by
  unfold coordEnergy
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp [coordMask, hi]
  · simp [coordMask, hi, sq_nonneg]

/-- For two nested coordinate spaces, the Pythagorean energy identity. -/
theorem coordMask_difference_energy {n : ℕ}
    (S T : Finset (Fin n)) (x : Fin n → ℝ) (h : S ⊆ T) :
    coordEnergy (fun i => coordMask T x i - coordMask S x i) +
      coordEnergy (coordMask S x) = coordEnergy (coordMask T x) := by
  unfold coordEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : i ∈ S
  · have ht : i ∈ T := h hs
    simp [coordMask, hs, ht]
  · by_cases ht : i ∈ T
    · simp [coordMask, hs, ht]
    · simp [coordMask, hs, ht]

/-- Discrete Bessel energy inequality for ANY finite nested family of
coordinate projection masks. Its bound does not depend on `N`. -/
theorem coordMask_chain_energy {n : ℕ}
    (S : ℕ → Finset (Fin n)) (x : Fin n → ℝ)
    (hS : ∀ k, S k ⊆ S (k+1)) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      coordEnergy (fun i => coordMask (S (k+1)) x i - coordMask (S k) x i))
      ≤ coordEnergy x := by
  have hdiff (k : ℕ) :
      coordEnergy (fun i => coordMask (S (k+1)) x i - coordMask (S k) x i) =
        coordEnergy (coordMask (S (k+1)) x) -
        coordEnergy (coordMask (S k) x) := by
    have h := coordMask_difference_energy (S k) (S (k+1)) x (hS k)
    linarith
  calc
    (∑ k ∈ Finset.range N,
        coordEnergy (fun i => coordMask (S (k+1)) x i - coordMask (S k) x i))
      = ∑ k ∈ Finset.range N,
          (coordEnergy (coordMask (S (k+1)) x) -
           coordEnergy (coordMask (S k) x)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact hdiff k
    _ = coordEnergy (coordMask (S N) x) - coordEnergy (coordMask (S 0) x) := by
          exact finite_telescoping (fun k => coordEnergy (coordMask (S k) x)) N
    _ ≤ coordEnergy x := by
          have h1 := coordMask_energy_le (S N) x
          have h0 : 0 ≤ coordEnergy (coordMask (S 0) x) := by
            unfold coordEnergy
            apply Finset.sum_nonneg
            intro i _
            exact sq_nonneg _
          linarith

end OpenAI086
