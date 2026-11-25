# V44: continuous local projections and refining cuts

Base: V43. Paper SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936` (93 pages, October 5 2026 manuscript). Source focus: Lemma 3.2 pp. 7–8 and Lemma 3.4 pp. 9–13.

## New source candidates

- `PaperV44L2Projection.lean`: finite span, finite-dimensional projection instance, actual orthogonal projection, coefficient representation, integrated normal equations, L² energy identity and refinement.
- `PaperV44PrivateRefit.lean`: actual complex Euclidean private-coordinate columns, synthesis representation, L² injectivity, unique coefficients, two-sided pointwise norm bounds and almost-everywhere D^5 estimate from projection orthogonality. The bound retains MemLp and input-norm integrability hypotheses. This is a source candidate, not a kernel-certified lemma.
- `PaperV44RefiningCuts.lean`: pointwise finite partition indicator sum, L² span inclusion when the coarse columns are represented by the refined columns, and actual nested-projection identity.

## Explicitly unresolved

- Lemma 3.2: compile and fix elaboration, obtain the MemLp and L1 hypotheses from the paper's measurable bounded column and probability measure assumptions, connect normalized Lebesgue interval measures and extract the scalar-input private-coordinate moment. Local selected-label Euclidean spaces must be related to the common ambient label Hilbert space.
- Lemma 3.4: instantiate the cut refinement for the actual inherited birth/mask family, build dyadic stopping trees and moment representatives, establish maximal and representative energies, construct and sum anchor attempts, and close the uniform polylogarithmic bound including complements and measure averages.
- Lemma 3.3 and corrected 3.5: existing proof candidates remain unverified.
- Weyl alternative, general quantitative U³ inverse theorem, localization, short-block comparisons, square energy, sparse density saving, absorption, and unconditional main theorem remain incomplete. No claims of completion made for these results.

## Verification

Run `bash verify_v44.sh` or `bash verify_v44.sh --target 3.2-projection`. GitHub Actions workflow `.github/workflows/lean-v44.yml` checks five targets independently. The projection module depends only on Mathlib, so unrelated repository failures should not prevent its targeted build. All targets still require review of the encoded statement against the manuscript; the verifier intentionally does not promote manuscript registry entries automatically. The V43 workflow is preserved.

Lean/Lake absent, and direct GitHub access failed DNS resolution. The verification log records exit 2 (blocked), not success. Static import/registry/source checks and Python tests of verifier behavior do not certify Lean proofs. The pinned toolchain and target statement lock remain unchanged. No new `sorry`, `admit`, or custom mathematical axioms were introduced. Public Mathlib API documentation was consulted for finite spans, L² inner products and Euclidean spaces; the exact pinned API and elaboration have not been checked by Lean.

Certified results: 0/58. Unconditional main theorem: 0/1.
