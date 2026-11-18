import OpenAI086
import OpenAI086.Lemma33Check

/-!
# Single whole-project entry point — OpenAI #086 (2026-10-05)

This file imports the existing independent core AND the reviewed (adapted)
Lemma 3.3 candidate, so `lake build OpenAI086Whole` cannot quietly skip it.

A successful build establishes kernel checking of declarations that actually
have proofs. It does NOT prove the paper's main Theorem 1.1, which remains
an explicitly UNPROVED proposition in `OpenAI086/PaperStatement.lean`.

The Lemma 3.3 candidate is adapted from a third-party source and is
attributed in `PROVENANCE.md`; it is not independent proof authorship.
-/

#check OpenAI086.Theorem1_1_Goal
#check OpenAI086.quadratic_resonance
#check OpenAI086.Lemma33.nestedProjectionProduct_prefix_rows_sq
#check OpenAI086.Lemma33.nestedProjectionProduct_successive_jumps

#print axioms OpenAI086.quadratic_resonance
#print axioms OpenAI086.Lemma33.nestedProjectionProduct_prefix_rows_sq
#print axioms OpenAI086.Lemma33.nestedProjectionProduct_successive_jumps
