# V48 — Coefficient transition, restart contraction, and anchor partitions

Source basis: October 5, 2026 manuscript, especially Lemma 3.4, pp. 10–12. The PDF SHA-256 remains unchanged and matches `verification/PAPER_SHA256.txt`.

## New source modules

- `OpenAI086/PaperV48PrivateTransition.lean`: converts a lower bound for movement of the finite coefficient vector into a lower bound for the actual augmented private-coordinate synthesis. This uses the lower Gram bound from the `D^{-1}` private amplitudes.
- `OpenAI086/PaperV48RestartCutoff.lean`: proves the numerical cutoff factor is below `1/2` for `tau=D^{-10}`, `b=2D(m+1)`, `L_T<=b^4`, and `T>=b^(128(m+1)^2)`.
- `OpenAI086/PaperV48SpatialAnchors.lean`: finite-horizon spatial anchor states, terminal-cell measurability, and terminal-cell labels.
- `OpenAI086/PaperV48RestartAssembly.lean`: defines the actual augmented-column increment; proves coefficient movement gives the pointwise squared increment lower bound; combines the restart integral bridge with the exact cutoff to give simultaneous half-contraction of restart-root measure and representative energy. The theorem explicitly assumes the nested-prefix variation estimate and the `D^5` representative-energy caps.
- `OpenAI086/PaperV48AnchorPartitions.lean`: constructs finite history-labelled anchor-stage atoms (active prefixes or terminal cells), proves stage refinement and measurability of their fibres.

## Exact scope of the V48 restart result

The theorem `v48_private_restart_attempt_contract` has eliminated the pointwise `hlarge` assumption from the generic restart bridge: it derives that lower bound from the actual pointwise augmented-column synthesis and a coefficient-motion assumption.

It has **not** derived the variation estimate from the concrete projection products. That still requires building the paper's full generation-by-generation partitions `pi_n`, showing their direct-sum local projections are nested, applying Lemma 3.3 to the actual `Z_n`, and identifying each `Z_n-Z_(n-1)` with the coefficient-synthesis increment almost everywhere.

The theorem also keeps explicit:

1. integrability of the increment norms;
2. the Lemma 3.3 variation budget;
3. the `D^5` global representative-energy cap;
4. the child-root pointwise-energy cap derived from the `L-infinity` representative bound.

Those assumptions are not hidden, and this conditional result is not the full Lemma 3.4.

## Anchor partition distinction

The new history-labelled partition is genuinely finite, measurable, and nested. For an active path its label is the prefix of all anchor depths and cells through the current generation; a terminated path is labelled by its full history and terminal cell. Prefix truncation proves refinement.

This history partition may be finer than the exact paper partition if distinct prior histories lead into the same current anchor cell. The next proof must show, from the ancestor consistency of coefficients and the first-match rule, that an active anchor cell determines its entire earlier anchor history. Only then can we quotient the history labels to exactly the paper's active-anchor atoms without creating unnecessary projection refinements or path-budget costs.

## Validation performed

- Static import audit: 308 independent Lean files reachable; no cycles or missing imports.
- Registry audit: updated to 924 theorem declarations and 308 Lean files.
- Lean source safety scan: no new `sorry`, `admit`, or custom axioms.
- Deterministic exact-model tests: 2,012 cases (restart cutoff, private-coordinate transitions, terminal-cell history consistency, and history-partition refinement).
- ZIP archive integrity checked at packaging.

These are source, bookkeeping, and exact finite-model checks, **not Lean kernel certificates**.

## Kernel disposition

Lean, Lake, and elan are absent in this environment; network DNS prevents installing the pinned toolchain. `tools/verify_v48_targets.py` records each attempted target as `BLOCKED: Lean/Lake unavailable` and exits nonzero. No target is promoted to kernel-verified. The GitHub Actions workflow is supplied but has not been executed here.

## Remaining mathematical work

1. Prove the history-prefix coherence theorem that collapses history labels onto exact anchor-cell atoms.
2. Construct the actual spatial partitions `pi_n` in each attempt, with active anchors plus terminal cut cells.
3. Prove inherited local span/projection nesting for the concrete masks on every atom.
4. Derive the pointwise transition lower bound for `(Z_n-Z_(n-1))(1_R g_K)`, rather than a generic finite synthesis with supplied coefficient fields.
5. Derive the full Lemma 3.3 variation budget for those `Z_n` products.
6. Derive integrability and both `D^5` energy caps from the actual moment representative.
7. Sum restart attempts across size segments, derive the representative-energy logarithmic bound, and assemble all row anchor/error terms, complements, and finite-measure averages to finish Lemma 3.4.
8. Continue Lemma 3.5 corrected vector/supremum conclusions; Section 4's full Weyl alternative and general quantitative `U^3` inverse theorem; Sections 5–6; Section 7; Section 8.9; Lemma 9.1; Section 10 absorption; then Theorem 1.1.

No paper result counts change: 0/58 numbered mathematical results are kernel-certified and Theorem 1.1 remains unproved.
