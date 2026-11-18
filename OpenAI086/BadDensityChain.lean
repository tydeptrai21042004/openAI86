import Mathlib
import OpenAI086.ErrataChecks

/-!
# OpenAI #086, Lemma 8.6: endpoint inclusion

The original displayed chain for `i < N` does not control the last
`P_N ⊆ C_N`. Here the endpoint hypothesis is stated separately and
simple set inclusions are deduced. This does NOT establish the whole
bad-density-chain bound.
-/

namespace OpenAI086

/-- With the corrected inclusion assumptions, successive P-sets are nested. -/
theorem corrected_chain_is_nested
    (P C : ℕ → Finset ℕ) (N : ℕ)
    (hPC : ∀ i ≤ N, P i ⊆ C i)
    (hCP : ∀ i < N, C i ⊆ P (i+1)) :
    ∀ i < N, P i ⊆ P (i+1) := by
  intro i hi
  exact (hPC i (Nat.le_of_lt hi)).trans (hCP i hi)

/-- The formerly missing terminal inclusion is now an explicit hypothesis. -/
theorem corrected_chain_last_endpoint
    (P C : ℕ → Finset ℕ) (N : ℕ)
    (hPC : ∀ i ≤ N, P i ⊆ C i) : P N ⊆ C N :=
  hPC N (le_refl N)

end OpenAI086
