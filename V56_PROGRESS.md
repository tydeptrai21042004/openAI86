# V56 — original-paper fidelity continuation of V55

The newly supplied `paper(9).pdf` is byte-for-byte identical to the original PDF in the repository (`paper(7).pdf`): SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`. The original main-theorem lock is unchanged. The V55 external sign and bounded-extension bridges are included in this full release, unchanged.

## New mathematical source

- `OpenAI086/PaperV56Lemma32.lean`: combines both actual pointwise coefficient inequalities, uniqueness of constant coefficients for the orthogonal L² projection, the D^5 bound, and the scalar-input moment identity on normalized probability measure. Derives L² membership of augmented columns from their essential bounds and measurability, and derives integrability of the L² input. The proof uses the existing independent V42–V45 machinery. Exact interval normalization, selected-label reindexing and kernel replay are still required before claiming the full printed lemma certified.
- `OpenAI086/PaperV56ExceptionalBlocks.lean`: proves the count for finite K-spaced block schedules (at most five starts per logarithmic packet), then derives a 5d count for a primary from the actual rational-height cover. This is the first assertion of Lemma 8.2, not the second rational-span assertion. The source paper's explicit application of Lemma 3.5 on pp.67–68 uses the packet-width bound in part (1), not the false bandwidth coefficient in part (2). This is a concrete downstream check; a complete audit of all implicit uses of the height lemma remains necessary.
- `source_fidelity/v56/EntryRank.lean`: attributed Apache-2.0 adaptation of the reference's first-entry grouping and telescoping harmonic proof (reference commit 7b4209609e6a7fb9d9935973ee8541495f943660). Added the exact H_M and log bounds, allowing M to be an upper bound on the final cardinality. Empty stage zero is the indexing convention. This standalone file uses Mathlib and is deliberately outside the independently derived OpenAI086 tree; it is not represented as independent authorship.

## Whole-paper fidelity

`verification/V56_PAPER_FIDELITY.md` and `.json` map all 59 numbered entries, including Definition 4.1, to the reference source and provide 54 declaration anchors checked for existence in the source. Unnumbered §10 obligations are also listed. A location or declaration name is not a certificate of equivalence. In particular:

- Lemma 3.5(2) cannot be proved as printed (see V42 counterexample). The corrected bandwidth factor must be explicitly documented.
- Theorem 4.7 is the general external LSS nilmanifold inverse theorem. The finite cyclic inverse theorem of the reference is a substitute for the main proof, not a proof of that exact theorem.
- Reference `columnSpatialCompression` has weaker dependence on m than the printed Lemma 3.4, assumes pointwise path counts, and uses common row codomain. Exact paper-level proof must address these differences, the complements and integral averaging assertion.
- Remaining analytic results and original parameter order cannot be marked complete merely because the reference proves a mathematically equivalent main theorem.

## Reproduction

`bash verify_v56.sh` executes integrity, source safety, registry, source-lock and 1,300 exact Python model tests, followed by actual Lean kernel checks if the pinned toolchain is installed. The verification command exits 2 in the authoring environment because Lean/Lake are missing. The separate adapted Lemma 8.5 is checked first in the Lean stage, followed by the whole independent tree and explicit axiom reports. V55 main-theorem replay remains available separately.

Actual result: source and model audits passed; 328 independent Lean files, 988 theorem declarations by the existing counter. Five new independent declarations and four adapted standalone declarations, none kernel-certified. 0/58 complete paper-level certificates. No new analytic assumptions were introduced as axioms. The original theorem remains open in the independent project. All proof candidates require compilation, and the adapted candidate may require adjustment for its isolated Mathlib import.
