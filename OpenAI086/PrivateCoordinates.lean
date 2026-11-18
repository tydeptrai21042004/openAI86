import Mathlib

/-!
# OpenAI #086, §3.2: elementary private-coordinate algebra

A column has a scalar physical coordinate and a private coordinate
`ε_i*c_i` unique to label `i`.  This file proves coefficient recovery in
that finite-coordinate model.  It does NOT prove the `D^5` local projection
bound of Lemma 3.2, which requires Hilbert-space Gram matrices and integrals.
-/

namespace OpenAI086

/-- Distinct coefficient vectors cannot have the same private coordinates
when every amplitude is nonzero. -/
theorem private_coordinates_recover_coefficients
    {n : ℕ} (ε c d : Fin n → ℝ)
    (hε : ∀ i, ε i ≠ 0)
    (h : ∀ i, ε i * c i = ε i * d i) : c = d := by
  funext i
  have hz : ε i * (c i - d i) = 0 := by
    rw [mul_sub]
    exact sub_eq_zero.mpr (h i)
  have hd : c i - d i = 0 := (mul_eq_zero.mp hz).resolve_left (hε i)
  exact sub_eq_zero.mp hd

/-- A private coordinate is zero exactly when its coefficient is zero. -/
theorem private_coordinate_zero
    (ε c : ℝ) (hε : ε ≠ 0) :
    ε * c = 0 ↔ c = 0 := by
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hε
  · intro h
    simp [h]

/-- The private-coordinate identity used in the Gram-matrix lower bound:
its squared contribution is always nonnegative. -/
theorem private_square_nonnegative (ε c : ℝ) :
    0 ≤ (ε * c) ^ 2 := sq_nonneg _

/-- If the squared private amplitudes are controlled below pointwise,
then the sum of squared private coordinates has that same lower bound. -/
theorem private_energy_lower_bound
    {n : ℕ} (ε c : Fin n → ℝ) (D : ℝ)
    (hD : 0 < D) (hε : ∀ i, 1 / D ≤ ε i) :
    (∑ i : Fin n, (c i / D) ^ 2) ≤
      (∑ i : Fin n, (ε i * c i) ^ 2) := by
  apply Finset.sum_le_sum
  intro i _
  have hsmall : 0 ≤ (1 : ℝ) / D := by positivity
  have hlarge : 0 ≤ ε i := le_trans hsmall (hε i)
  have hprod : 0 ≤ (ε i - 1 / D) * (ε i + 1 / D) :=
    mul_nonneg (sub_nonneg.mpr (hε i)) (add_nonneg hlarge hsmall)
  have hsq : (1 / D) ^ 2 ≤ (ε i) ^ 2 := by nlinarith [hprod]
  calc
    (c i / D) ^ 2 = (1 / D) ^ 2 * (c i) ^ 2 := by ring
    _ ≤ (ε i) ^ 2 * (c i) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = (ε i * c i) ^ 2 := by ring

end OpenAI086
