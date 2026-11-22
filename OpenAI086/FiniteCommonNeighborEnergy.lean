import Mathlib
import OpenAI086.FiniteRowCauchySchwarz

/-!
# Lemma 9.1: the exact common-neighbor / second-moment step

For a finite bipartite graph with real edge weights `a(u,v)`, the
sum of codegrees over ordered left-vertex pairs equals the second
moment of right-vertex degrees. Cauchy--Schwarz gives the quantitative
lower bound after multiplying by the size of the right part.

For 0/1 weights this counts ordered two-edge paths, with repeated
endpoints allowed. This is a genuine finite counting lemma used in
the graph-density part of the sparse-count proof, not the full
four-step path argument or the `δ^(1/2080)` saving.
-/

namespace OpenAI086

/-- Double counting ordered two-edge paths by their central vertex. -/
theorem finite_common_neighbor_identity
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) :
    (∑ u : U, ∑ w : U, ∑ v : V, a u v * a w v) =
      ∑ v : V, (∑ u : U, a u v) ^ 2 := by
  classical
  have hcenter (v : V) :
      (∑ u : U, ∑ w : U, a u v * a w v) =
        (∑ u : U, a u v) ^ 2 := by
    calc
      (∑ u : U, ∑ w : U, a u v * a w v) =
          ∑ u : U, a u v * (∑ w : U, a w v) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
      _ = (∑ u : U, a u v) * (∑ w : U, a w v) := by
            rw [Finset.sum_mul]
      _ = (∑ u : U, a u v) ^ 2 := by ring
  calc
    (∑ u : U, ∑ w : U, ∑ v : V, a u v * a w v) =
        ∑ u : U, ∑ v : V, ∑ w : U, a u v * a w v := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_comm]
    _ = ∑ v : V, ∑ u : U, ∑ w : U, a u v * a w v := by
          rw [Finset.sum_comm]
    _ = ∑ v : V, (∑ u : U, a u v) ^ 2 := by
          apply Finset.sum_congr rfl
          intro v _
          exact hcenter v

/-- Quantitative second-moment inequality: the total edge weight
squared is at most the number of right vertices times the total
ordered common-neighbor mass. No graph regularity is assumed. -/
theorem finite_common_neighbor_second_moment
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) :
    (∑ v : V, ∑ u : U, a u v) ^ 2 ≤
      (Fintype.card V : ℝ) *
        (∑ u : U, ∑ w : U, ∑ v : V, a u v * a w v) := by
  have hcs := finite_row_cauchy_schwarz
    (fun v : V => ∑ u : U, a u v) (fun _v : V => (1 : ℝ))
  rw [finite_common_neighbor_identity a]
  simpa [mul_comm] using hcs

end OpenAI086
