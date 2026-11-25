# V45 — scalar normal equation and disjoint cut refits

Base: V44. The supplied 93-page manuscript has SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`, matching `verification/PAPER_SHA256.txt`. Source focus: Lemma 3.2 (p. 8), Lemma 3.4 (pp. 10–11).

## New Lean proof candidates

- `PaperV45ScalarMoment.lean`: evaluates the inner product against a private column using its physical and private coordinates; embeds a scalar input with zero private coordinates; derives the scalar normal equation from the constructed actual L² projection and its orthogonality. The last theorem uses `a = sqrt ε` and gives the paper's `ε_v c_v` factor. The input and columns are explicitly assumed to belong to L²; integrability of the residual pairing is handled by L² inner products. This still needs the normalized-interval and bounded-measurable-column interfaces, and kernel checking.
- `PaperV45CutRefit.lean`: derives orthogonality from disjoint supports of L² vectors; constructs each local refit on cut-supported columns; proves moment preservation, the global energy identity, and equality of coarse projections when each inherited column restricts to a fine column on each cut atom. The finite cut, inherited restrictions and MemLp witnesses are explicit inputs; their construction from the stopping rules is not proved here.

## Remaining obligations

- Lemma 3.2: kernel checking, actual normalized interval measures, common ambient label space and automatic square-integrability of bounded measurable columns. The scalar moment now has a proof candidate, not a certified manuscript theorem.
- Lemma 3.3: previous joint candidate remains uncompiled.
- Lemma 3.4: concrete stopping tree, bounded representatives with normalized local projection estimates, maximal-function and summed representative energy estimates, anchors, two simultaneous restart bounds, final polylogarithmic estimate, complements and measure averages.
- Corrected Lemma 3.5, quantitative Weyl alternative, general quantitative inverse U³, localization, short blocks, square energy, sparse-density saving, normalized absorption and Theorem 1.1 remain open or uncompiled. No proof-completion flags changed.

## Verification

`bash verify_v45.sh` ran static checks and eight Python verifier unit tests. It exited 2 because `lean` and `lake` are absent; direct GitHub access failed DNS resolution. Reports for all three targeted declarations record BLOCKED. No Lean result has been certified. The exact rational finite-model tests in `tools/test_v45_models.py` passed 12 scalar and 12 cut examples (run separately with SymPy). They test algebraic identities, not arbitrary continuous hypotheses or proof elaboration.

On a Lean-enabled host, run `bash verify_v45.sh --target 3.2-scalar`, `--target 3.4-moment`, or `--target 3.4-energy`. The V45 workflow is available for GitHub Actions; it has not run here. Source candidates may need elaboration repairs, including inherited dependencies. No new proof placeholders or mathematical axioms were added. Only encoded statements that pass build and strict axiom checking can be marked kernel-checked; manuscript statement fidelity must additionally be reviewed.

297 independent Lean files; 868 theorem declarations; 0/58 fully kernel-certified mathematical results; 0/1 unconditional main theorem.
