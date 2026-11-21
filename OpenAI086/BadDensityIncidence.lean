import Mathlib
import OpenAI086.InterleavedGapBudget

/-!
# OpenAI #086, Lemma 8.6: the finite incidence-to-chain-length step

This proves the final *quantitative counting implication* from page 70.
It assumes (rather than asserts) the two genuinely difficult upstream
bounds: each position has enough bad heights, and the aggregate incidences
have the stated upper budget. In particular it does NOT prove the full
bad-density-chain lemma or its entry-rank/height hypotheses.

Here `H` is the number of heights (the paper writes `J + 1`), `Q` is the
per-position error budget, and `R` is the per-height error budget.
-/

namespace OpenAI086

/-- From a lower bound on bad-height incidences and a global upper bound,
prove the numerical chain-length conclusion (in non-strict form). -/
theorem bad_density_incidence_chain_bound
    (N H : ℕ) (δ Q R : ℝ) (counts : Fin N → Fin H → ℝ)
    (hδ : 0 < δ) (hH : 0 < H)
    (hbudget : 2 * Q ≤ δ * (H : ℝ))
    (hlower : ∀ i : Fin N,
      δ * (H : ℝ) ≤ ∑ h : Fin H, counts i h)
    (hupper : (∑ i : Fin N, ∑ h : Fin H, counts i h) ≤
      (N : ℝ) * Q + (H : ℝ) * R) :
    (N : ℝ) ≤ 2 * R / δ := by
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have htotalLower :
      (N : ℝ) * (δ * (H : ℝ)) ≤
        ∑ i : Fin N, ∑ h : Fin H, counts i h := by
    calc
      (N : ℝ) * (δ * (H : ℝ)) = ∑ _i : Fin N, δ * (H : ℝ) := by simp
      _ ≤ ∑ i : Fin N, ∑ h : Fin H, counts i h := by
        apply Finset.sum_le_sum
        intro i _
        exact hlower i
  have hQ : (N : ℝ) * (2 * Q) ≤
      (N : ℝ) * (δ * (H : ℝ)) :=
    mul_le_mul_of_nonneg_left hbudget hNnonneg
  have hscaled : (N : ℝ) * δ * (H : ℝ) ≤
      (2 * R) * (H : ℝ) := by
    nlinarith [htotalLower, hupper, hQ]
  have hconclusion : (N : ℝ) * δ ≤ 2 * R := by
    by_contra hnot
    have hlt : 2 * R < (N : ℝ) * δ := lt_of_not_ge hnot
    have hscaledLt := mul_lt_mul_of_pos_right hlt hHpos
    linarith
  exact (le_div_iff₀ hδ).2 hconclusion

end OpenAI086
