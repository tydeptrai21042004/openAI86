import Mathlib

/-!
# V6: finite catalog closure for manuscript Lemmas 6.4 and 6.7

Actual catalog construction is on dyadic cells and involves quantitative
phase geometry.  This module proves only the finite set-theoretic core:
closure is extensive and monotone, its iterates are nested, and any
closed supersets contain every iterate.  These are independently useful
proof components, not the whole localization lemmas.
-/

namespace OpenAI086

/-- Add every vertex already in `s`, together with every neighbor
listed by a vertex in `s`. -/
def finiteCatalogStep {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Finset V) : Finset V :=
  s ∪ s.biUnion neighbors

theorem finite_catalog_step_extensive {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Finset V) :
    s ⊆ finiteCatalogStep neighbors s := by
  intro v hv
  exact Finset.mem_union.mpr (Or.inl hv)

theorem finite_catalog_step_monotone {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) {s t : Finset V} (h : s ⊆ t) :
    finiteCatalogStep neighbors s ⊆ finiteCatalogStep neighbors t := by
  intro v hv
  rcases Finset.mem_union.mp hv with hbase | hstep
  · exact Finset.mem_union.mpr (Or.inl (h hbase))
  · rcases Finset.mem_biUnion.mp hstep with ⟨u, hu, huv⟩
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_biUnion.mpr ⟨u, h hu, huv⟩))

/-- A fixed number of synchronous catalog-closure rounds. -/
def finiteCatalogIterate {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Finset V) : ℕ → Finset V
  | 0 => s
  | n + 1 => finiteCatalogStep neighbors (finiteCatalogIterate neighbors s n)

/-- The catalog can only gain entries as the number of rounds grows. -/
theorem finite_catalog_iterate_nested {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Finset V) (n : ℕ) :
    finiteCatalogIterate neighbors s n ⊆
      finiteCatalogIterate neighbors s (n + 1) := by
  exact finite_catalog_step_extensive neighbors _

/-- More initial labels can only increase each subsequent closure. -/
theorem finite_catalog_iterate_monotone {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) {s t : Finset V}
    (h : s ⊆ t) (n : ℕ) :
    finiteCatalogIterate neighbors s n ⊆
      finiteCatalogIterate neighbors t n := by
  induction n with
  | zero => exact h
  | succ n ih => exact finite_catalog_step_monotone neighbors ih

/-- Closed supersets contain every finite iterate. No finite size
bound on the catalog is assumed. -/
theorem finite_catalog_iterate_in_closed_set
    {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V)
    (s t : Finset V) (hstart : s ⊆ t)
    (hclosed : ∀ v ∈ t, neighbors v ⊆ t)
    (n : ℕ) : finiteCatalogIterate neighbors s n ⊆ t := by
  induction n with
  | zero => exact hstart
  | succ n ih =>
      intro v hv
      change v ∈ (finiteCatalogIterate neighbors s n ∪
        (finiteCatalogIterate neighbors s n).biUnion neighbors) at hv
      rcases Finset.mem_union.mp hv with hbase | hstep
      · exact ih hbase
      · rcases Finset.mem_biUnion.mp hstep with ⟨u, hu, huv⟩
        exact hclosed u (ih hu) huv

end OpenAI086
