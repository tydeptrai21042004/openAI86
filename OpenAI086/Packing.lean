import Mathlib
import OpenAI086.FiniteReductions

/-!
# OpenAI #086, Lemma 3.1: scalar finite-generation packing

This formalizes the complete *scalar consequence* of a one-step
root-mass contraction. It does not formalize dyadic intervals, the
algorithm producing disjoint children, or their measurable lengths.
-/

namespace OpenAI086

/-- A geometric sum with ratio in `[0,1)` is bounded independently of `N`. -/
theorem geometric_sum_uniform (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, ρ ^ n) ≤ 1 / (1-ρ) := by
  have hpos : 0 < 1-ρ := by linarith
  have hgeom : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, ρ ^ k) * (1-ρ) = 1-ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith [ih]
  apply (le_div_iff₀ hpos).2
  have hpow : 0 ≤ ρ ^ N := pow_nonneg hρ0 N
  nlinarith [hgeom N]

/-- The generation-by-generation packing estimate with a uniform
bound independent of the number of generations. -/
theorem packing_of_contracted_generations
    (mass : ℕ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hroot : 0 ≤ mass 0)
    (hstep : ∀ n, mass (n+1) ≤ ρ*mass n)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, mass n) ≤ mass 0 / (1-ρ) := by
  have hpoint := decay_of_contraction mass ρ hρ0 hstep
  calc
    (∑ n ∈ Finset.range N, mass n)
        ≤ ∑ n ∈ Finset.range N, ρ ^ n * mass 0 := by
            apply Finset.sum_le_sum
            intro n _
            exact hpoint n
    _ = (∑ n ∈ Finset.range N, ρ ^ n) * mass 0 := by
            rw [Finset.sum_mul]
    _ ≤ (1/(1-ρ)) * mass 0 :=
            mul_le_mul_of_nonneg_right
              (geometric_sum_uniform ρ hρ0 hρ1 N) hroot
    _ = mass 0 / (1-ρ) := by ring

/-- If the cost of a generation is at most `A` times its mass,
the total cost is bounded by `A` times the root packing constant. -/
theorem cost_of_packed_generations
    (mass cost : ℕ → ℝ) (A ρ : ℝ)
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hroot : 0 ≤ mass 0)
    (hstep : ∀ n, mass (n+1) ≤ ρ*mass n)
    (hcost : ∀ n, cost n ≤ A*mass n)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, cost n) ≤ A*mass 0/(1-ρ) := by
  calc
    (∑ n ∈ Finset.range N, cost n)
        ≤ (∑ n ∈ Finset.range N, A*mass n) := by
          apply Finset.sum_le_sum
          intro n _
          exact hcost n
    _ = A*(∑ n ∈ Finset.range N, mass n) := by
          rw [Finset.mul_sum]
    _ ≤ A*(mass 0 / (1-ρ)) :=
          mul_le_mul_of_nonneg_left
            (packing_of_contracted_generations mass ρ hρ0 hρ1 hroot hstep N) hA
    _ = A*mass 0/(1-ρ) := by ring

end OpenAI086
