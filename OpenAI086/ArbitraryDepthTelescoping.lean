import Mathlib

/-!
# OpenAI #086, Lemma 3.3: independent arbitrary-depth ordered telescoping

Unlike the external Rademacher--Menshov code, this proof is authored here
and uses only standard Mathlib additive homomorphisms.  It works with an
arbitrary finite list of (new, old) endomorphism pairs, even when different
operators do not commute.  The `error` field exactly records the sum of
successively propagated changes. The logarithmic square-function bound
required by Lemma 3.3 remains an independent analytic obligation.
-/

namespace OpenAI086

structure OrderedTelescopingState (E : Type*) where
  current : E
  previous : E
  error : E

/-- One noncommuting layer: update both products and propagate the error. -/
def orderedTelescopingStep
    {E : Type*} [AddCommGroup E]
    (s : OrderedTelescopingState E)
    (pq : (E →+ E) × (E →+ E)) : OrderedTelescopingState E :=
  { current := pq.1 s.current
    previous := pq.2 s.previous
    error := pq.1 s.error + (pq.1 s.previous - pq.2 s.previous) }

/-- At each new layer the propagated error equals the difference between
the new and old ordered products. No commutativity is invoked. -/
theorem orderedTelescopingStep_invariant
    {E : Type*} [AddCommGroup E]
    (s : OrderedTelescopingState E)
    (pq : (E →+ E) × (E →+ E))
    (h : s.error = s.current - s.previous) :
    (orderedTelescopingStep s pq).error =
      (orderedTelescopingStep s pq).current -
        (orderedTelescopingStep s pq).previous := by
  change pq.1 s.error + (pq.1 s.previous - pq.2 s.previous) =
    pq.1 s.current - pq.2 s.previous
  rw [h, map_sub]
  abel

/-- Arbitrary-depth telescoping invariant established by induction on
an actual list of ordered endomorphism pairs. -/
theorem orderedTelescopingFold_invariant
    {E : Type*} [AddCommGroup E]
    (pairs : List ((E →+ E) × (E →+ E)))
    (s : OrderedTelescopingState E)
    (h : s.error = s.current - s.previous) :
    (pairs.foldl orderedTelescopingStep s).error =
      (pairs.foldl orderedTelescopingStep s).current -
        (pairs.foldl orderedTelescopingStep s).previous := by
  induction pairs generalizing s with
  | nil => simpa using h
  | cons pq rest ih =>
      simp only [List.foldl_cons]
      exact ih (orderedTelescopingStep s pq)
        (orderedTelescopingStep_invariant s pq h)

/-- An arbitrary number of noncommuting layers satisfies the exact ordered
telescoping formula computed by the error accumulator. -/
theorem arbitrary_depth_ordered_telescoping
    {E : Type*} [AddCommGroup E]
    (pairs : List ((E →+ E) × (E →+ E))) (z : E) :
    (pairs.foldl orderedTelescopingStep
      ⟨z, z, (0 : E)⟩).error =
    (pairs.foldl orderedTelescopingStep
      ⟨z, z, (0 : E)⟩).current -
    (pairs.foldl orderedTelescopingStep
      ⟨z, z, (0 : E)⟩).previous := by
  apply orderedTelescopingFold_invariant
  simp

end OpenAI086
