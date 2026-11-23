import Mathlib
import OpenAI086.FiniteRowCauchySchwarz
import OpenAI086.GeneralNestedProjectionEnergy

/-!
# Lemma 3.3: sharp layer-count factor in telescoping variations

Before the paper uses its variable-prefix Bessel lemma, it expands a
noncommuting product difference into m summands and invokes Cauchy--
Schwarz over those m layers. This independent finite-real theorem gives
exactly the required factor m (not m²) times the total layer energy.

The missing next step is to show each layer energy is controlled by
one of the nested-prefix inequalities. The theorem below is an
unconditional Hilbert-sum inequality, not the full variation bound.
-/

namespace OpenAI086

/-- Energy of a sum of m ordered-layer contributions is at most m
 times the sum of their individual energies, summed over ALL depths.
 The constant m is sharp when every layer contribution is identical. -/
theorem finite_layer_variation_cauchy_schwarz
    {T m d : ℕ} (v : Fin T → Fin m → Fin d → ℝ) :
    (∑ n : Fin T,
      finiteRealPair (∑ i : Fin m, v n i)
                     (∑ i : Fin m, v n i)) ≤
      (m : ℝ) *
        (∑ i : Fin m, ∑ n : Fin T, finiteRealPair (v n i) (v n i)) := by
  classical
  have hpoint (n : Fin T) (j : Fin d) :
      (∑ i : Fin m, v n i j) * (∑ i : Fin m, v n i j) ≤
        (m : ℝ) * (∑ i : Fin m, v n i j * v n i j) := by
    have h := finite_row_cauchy_schwarz
      (fun i : Fin m => v n i j) (fun _i : Fin m => (1 : ℝ))
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  have hsum :
      (∑ n : Fin T, ∑ j : Fin d,
        (∑ i : Fin m, v n i j) * (∑ i : Fin m, v n i j)) ≤
      ∑ n : Fin T, ∑ j : Fin d,
        (m : ℝ) * (∑ i : Fin m, v n i j * v n i j) := by
    apply Finset.sum_le_sum
    intro n _
    apply Finset.sum_le_sum
    intro j _
    exact hpoint n j
  have hleft :
      (∑ n : Fin T,
        finiteRealPair (∑ i : Fin m, v n i)
                       (∑ i : Fin m, v n i)) =
      ∑ n : Fin T, ∑ j : Fin d,
        (∑ i : Fin m, v n i j) * (∑ i : Fin m, v n i j) := by
    simp only [finiteRealPair, Finset.sum_apply]
  have hright :
      (∑ n : Fin T, ∑ j : Fin d,
        (m : ℝ) * (∑ i : Fin m, v n i j * v n i j)) =
      (m : ℝ) *
        (∑ i : Fin m, ∑ n : Fin T, finiteRealPair (v n i) (v n i)) := by
    simp only [finiteRealPair]
    have hswap :
        (∑ n : Fin T, ∑ j : Fin d, ∑ i : Fin m,
          v n i j * v n i j) =
        (∑ i : Fin m, ∑ n : Fin T, ∑ j : Fin d,
          v n i j * v n i j) := by
      calc
        (∑ n : Fin T, ∑ j : Fin d, ∑ i : Fin m,
          v n i j * v n i j) =
            ∑ n : Fin T, ∑ i : Fin m, ∑ j : Fin d,
              v n i j * v n i j := by
                apply Finset.sum_congr rfl
                intro n _
                rw [Finset.sum_comm]
        _ = ∑ i : Fin m, ∑ n : Fin T, ∑ j : Fin d,
              v n i j * v n i j := by rw [Finset.sum_comm]
    calc
      (∑ n : Fin T, ∑ j : Fin d,
        (m : ℝ) * (∑ i : Fin m, v n i j * v n i j)) =
          (m : ℝ) *
            (∑ n : Fin T, ∑ j : Fin d, ∑ i : Fin m,
              v n i j * v n i j) := by simp only [Finset.mul_sum]
      _ = _ := by rw [hswap]
  rw [← hleft, hright] at hsum
  exact hsum

end OpenAI086
