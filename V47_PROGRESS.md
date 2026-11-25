# V47: measured maximal estimate and anchor construction

Source: October 5, 2026 manuscript, pp. 10–12. The attached paper's SHA-256 exactly matches verification/PAPER_SHA256.txt. V46 source is preserved except for the root import header and metadata; all mathematical additions are in three new modules.

## Proof candidates (not kernel-checked)

- `PaperV47MeasuredMaximal.lean`: integration over finite measurable partitions; integral of a cell-constant function; unnormalized Jensen; continuous finite-depth maximal squared bound 4 via exact terminal means; equality between coarse integrals and sums of leaf integrals; actual coarse average equality for positive-mass leaves.
- `PaperV47StoppingBudget.lean`: stopping-list/selected-depth energy identity and measured integrated path estimate with constant 16/3. This integrates the actual size-stop list, rather than assuming its bound.
- `PaperV47AnchorPath.lean`: coefficient-motion anchor selection with strict threshold, successive anchor gaps, retained coefficient error, and prefix consistency. No restart partition is constructed here.

## Remaining gaps

The abstract finite measurable partition must be instantiated from the manuscript's dyadic interval tree, with all terminal atoms and ancestor maps explicitly defined. The stopping-path integral needs the spatial-root sum identification. For the full representative-energy bound, the low/high root estimates must be connected to the actual cut-refit representatives, including a.e. support and integrability. The coefficient-motion path must be assembled into a stopping partition per attempt, with the T-th-transition restart rule and actual local products linked to Lemma 3.3. V38's restart estimate is conditional on increment and variation bounds; V47 does not discharge these conditions. The explicit cutoff T and polylogarithmic constant, complements and averaging are also open. All later manuscript results remain partial; the general inverse theorem remains an external proof obligation. The correction to Lemma 3.5(2) remains necessary.

## Validation

`bash verify_v47.sh`: static import, registry, independence, source safety and inventory checks pass; 8 mocked verifier tests pass; 1,000 exact rational model cases pass. Lean/Lake unavailable, exit 2. No manuscript certification is promoted. The model tests are not mathematical proofs. Use the pinned toolchain and `bash verify_v47.sh --target 3.4-maximal` on a Lean-enabled machine; separate targets check coarse averages, stopping budget, anchor chain and retained error. The CI workflow is provided but has not been executed here. No new proof placeholders or custom axioms were introduced.
