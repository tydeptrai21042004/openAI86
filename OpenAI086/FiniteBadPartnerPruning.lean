import Mathlib

/-!
# Finite bad-partner deletion: the Markov step of Lemma 9.1

Nonnegative bad-partner weights can be summed either by vertex or by
partner. If the total mass is small, the total threshold mass of
vertices with many bad partners is small. This is only the elementary
pruning implication; it neither constructs the dense graph of the
manuscript nor proves its power-saving sparse-count conclusion.
-/

namespace OpenAI086

/-- Finite weighted Markov inequality in indicator form. A vertex
which crosses the threshold contributes one entire threshold unit. -/
theorem finite_heavy_row_indicator_bound
    {U : Type*} [Fintype U]
    (mass : U → ℝ) (threshold : ℝ)
    (hmass : ∀ u, 0 ≤ mass u) :
    (∑ u : U, if threshold ≤ mass u then threshold else 0) ≤
      ∑ u : U, mass u := by
  classical
  apply Finset.sum_le_sum
  intro u _
  split_ifs with h
  · exact h
  · exact hmass u

/-- The row sums of a nonnegative finite bipartite weight have total
mass equal to the column sums, without regularity assumptions. -/
theorem finite_partner_mass_double_count
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) :
    (∑ u : U, ∑ v : V, a u v) =
      ∑ v : V, ∑ u : U, a u v := by
  classical
  exact Finset.sum_comm

/-- Quantitative deletion for vertices with excessive total bad-partner
mass; the only assumptions are nonnegativity and a total mass budget.
The threshold count is kept as an exact indicator sum. -/
theorem finite_bad_partner_pruning
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) (threshold budget : ℝ)
    (ha : ∀ u v, 0 ≤ a u v)
    (hbudget : (∑ v : V, ∑ u : U, a u v) ≤ budget) :
    (∑ u : U, if threshold ≤ (∑ v : V, a u v)
      then threshold else 0) ≤ budget := by
  have hmass (u : U) : 0 ≤ ∑ v : V, a u v := by
    apply Finset.sum_nonneg
    intro v _
    exact ha u v
  calc
    (∑ u : U, if threshold ≤ (∑ v : V, a u v)
        then threshold else 0) ≤
      ∑ u : U, ∑ v : V, a u v :=
        finite_heavy_row_indicator_bound
          (fun u => ∑ v : V, a u v) threshold hmass
    _ = ∑ v : V, ∑ u : U, a u v :=
      finite_partner_mass_double_count a
    _ ≤ budget := hbudget

end OpenAI086
