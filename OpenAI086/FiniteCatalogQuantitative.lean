import Mathlib
import OpenAI086.FiniteCatalogClosure
import OpenAI086.FiniteMultifamilyStops

/-!
# Finite quantitative catalog closure (manuscript §6.4 and §6.7)

The V6 catalog module proved extensivity, monotonicity and minimality
of an iterated closure. This file proves an explicit **cardinality**
budget from a bound on the number of neighbors of each label.

The manuscript also requires quantitative bounds on the geometric
catalogs along dyadic paths; these do NOT follow from this elementary
exponential bound and remain open.
-/

namespace OpenAI086

/-- A single catalog expansion with at most `B` neighbors per label
has no more than `(B+1)` times the original number of labels. -/
theorem finite_catalog_step_card_growth
    {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Finset V) (B : ℕ)
    (hdegree : ∀ v : V, (neighbors v).card ≤ B) :
    (finiteCatalogStep neighbors s).card ≤ (B + 1) * s.card := by
  classical
  have hunion := Finset.card_union_le s (s.biUnion neighbors)
  have hneigh := finite_biUnion_card_le_sum s neighbors
  have hbudget : (∑ v ∈ s, (neighbors v).card) ≤
      ∑ _v ∈ s, B := by
    apply Finset.sum_le_sum
    intro v _
    exact hdegree v
  calc
    (finiteCatalogStep neighbors s).card ≤
        s.card + (s.biUnion neighbors).card := by
          simpa only [finiteCatalogStep] using hunion
    _ ≤ s.card + ∑ v ∈ s, (neighbors v).card :=
        Nat.add_le_add_left hneigh _
    _ ≤ s.card + ∑ _v ∈ s, B := Nat.add_le_add_left hbudget _
    _ = (B + 1) * s.card := by simp [add_mul, mul_comm]

/-- A deterministic finite bound after any specified number of
catalog closure rounds. No limit or number-of-depths assumption. -/
theorem finite_catalog_iterate_card_growth
    {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Finset V) (B : ℕ)
    (hdegree : ∀ v : V, (neighbors v).card ≤ B)
    (n : ℕ) :
    (finiteCatalogIterate neighbors s n).card ≤
      (B + 1) ^ n * s.card := by
  induction n with
  | zero => simp [finiteCatalogIterate]
  | succ n ih =>
      calc
        (finiteCatalogIterate neighbors s (n + 1)).card ≤
            (B + 1) * (finiteCatalogIterate neighbors s n).card := by
              exact finite_catalog_step_card_growth neighbors
                (finiteCatalogIterate neighbors s n) B hdegree
        _ ≤ (B + 1) * ((B + 1) ^ n * s.card) :=
          Nat.mul_le_mul_left _ ih
        _ = (B + 1) ^ (n + 1) * s.card := by
          simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

end OpenAI086
