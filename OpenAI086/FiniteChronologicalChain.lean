import Mathlib
import OpenAI086.ChronologicalHarmonic

/-!
# Lemma 8.5 on an arbitrary finite nested chain

An arbitrary finite chain need not contain every label in its ambient
universe. Extend the chain by the full universe *only after* its last
tested index. This preserves all fractions and exception incidences on
the original chain, gives automatic coverage of all labels, and lets
the chronological rank proof apply without artificial assumptions.

The resulting theorem has exactly the finite-chain hypotheses of the
combinatorial counting lemma, rather than assuming given entry ranks.
-/

namespace OpenAI086

/-- Extend a finite family by the full universe after the final
observation. No extra labels appear at any tested time. -/
noncomputable def extendFiniteChain {M T : ℕ}
    (S : Fin T → Finset (Fin M)) (t : ℕ) : Finset (Fin M) :=
  if ht : t < T then S ⟨t, ht⟩ else Finset.univ

/-- The extension is exactly the original family at every test index. -/
theorem extend_finite_chain_at {M T : ℕ}
    (S : Fin T → Finset (Fin M)) (t : Fin T) :
    extendFiniteChain S t.val = S t := by
  classical
  simp [extendFiniteChain, t.isLt]

/-- Monotonicity of the extension, including its one transition from
an arbitrary terminal observed set to the full label universe. -/
theorem extend_finite_chain_mono {M T : ℕ}
    (S : Fin T → Finset (Fin M))
    (hmono : Monotone S) :
    Monotone (extendFiniteChain S) := by
  classical
  intro a b hab
  by_cases ha : a < T
  · by_cases hb : b < T
    · simpa [extendFiniteChain, ha, hb] using
        (hmono (show (⟨a, ha⟩ : Fin T) ≤ ⟨b, hb⟩ from hab))
    · simp [extendFiniteChain, ha, hb]
  · have hb : ¬ b < T := by omega
    simp [extendFiniteChain, ha, hb]

/-- All labels have entered by time T in the extended family. -/
theorem extend_finite_chain_cover {M T : ℕ}
    (S : Fin T → Finset (Fin M)) :
    ∀ r : Fin M, ∃ t : ℕ, r ∈ extendFiniteChain S t := by
  classical
  intro r
  refine ⟨T, ?_⟩
  simp [extendFiniteChain]

/-- Arbitrary finite nested-set version of the manuscript's first-entry
harmonic incidence lemma, with no rank/entry-time/coverage hypotheses.
The only quantitative assumption is the per-label exception count A.

The sum includes intersections E_t ∩ S_t and has a well-defined zero
contribution whenever S_t is empty (real division by zero is zero).
For the paper's nonempty-set version this convention is irrelevant. -/
theorem finite_chronological_harmonic_density
    {M T : ℕ}
    (S E : Fin T → Finset (Fin M))
    (hmono : Monotone S)
    (A : ℝ)
    (hinc : ∀ r : Fin M,
      (∑ t : Fin T,
        if r ∈ E t ∩ S t then (1 : ℝ) else 0) ≤ A) :
    (∑ t : Fin T,
      (((E t ∩ S t).card : ℝ) / ((S t).card : ℝ))) ≤
      A * finiteRankHarmonic M := by
  classical
  let S' : ℕ → Finset (Fin M) := extendFiniteChain S
  have hcover : ∀ r : Fin M, ∃ t : ℕ, r ∈ S' t :=
    extend_finite_chain_cover S
  have hmono' : Monotone S' := extend_finite_chain_mono S hmono
  have hinc' : ∀ r : Fin M,
      (∑ t : Fin T,
        if r ∈ E t ∩ S' t.val then (1 : ℝ) else 0) ≤ A := by
    intro r
    simpa only [S', extend_finite_chain_at] using hinc r
  have h := chronological_exception_fraction_harmonic
    S' E hcover hmono' A hinc'
  simpa only [S', extend_finite_chain_at] using h

end OpenAI086
