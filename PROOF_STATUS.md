# Independent proof status — OpenAI #086

**Requested target:** Theorem 1.1 of the 93-page manuscript, including the principal-value trilinear Hilbert transform and its unique bounded `L³ × L³ × L³ → L¹` extension.

**Status: UNPROVED IN THIS REPOSITORY.** There is no independent `theorem ... : Theorem1_1_Goal := by ...` proof, and no entire-paper Lean kernel certificate.

| Checkpoint | Status |
|---|---|
| Named results indexed from the PDF | 59/59 |
| Results with some related Lean components | 17/59 (partial only) |
| Complete paper results certified in independent Lean | 0/59 |
| Original target statement `Theorem1_1_Goal : Prop` | Present, unproved |
| Imported published trilinear Hilbert proof | NO |
| Adapted published Lemma 3.3 proof code | EXCLUDED |
| Independent ordered-telescoping proof | Source present, kernel check pending |
| Full Lemma 3.3, projection compression, quantitative Weyl, §§5–10 | OPEN |
| Static source/import checks | PASS at package creation |
| Lean kernel | UNVERIFIED — no Lean/Lake toolchain in runtime |

The 95 `theorem` declarations counted by source inventory are **smaller intermediate or model results**; they must not be confused with 84 independently proved assertions of the paper. Some have not been compiled by Lean yet.

For a statement-by-statement audit, consult `verification/PAPER_RESULTS_INDEX.md`.

## Continuation: additional independent components

Five new files cover specific, exact intermediate combinatorial implications in Lemmas 8.5, 8.10, and 9.1; they are not complete proofs of those lemmas. The number of named paper results with **some** Lean component increased from 16 to 17. None of the 59 results is fully kernel-verified. The additional Lean declarations have not been compiled in this environment.

The `TrilinearHT`-dependent integration remains excluded. The standalone Theorem 1.1 proposition continues to be a proof obligation without an independent proof term. The strict certificate must fail.
