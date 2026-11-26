# V58 — source-faithful continuation

Original manuscript: `paper(7).pdf`, SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`. No changes to the independent statement lock, source tree, or 59-result registry. The independent kernel-certified count is still zero.

## Lemma 7.2 (pp. 53–57)

Two isolated Mathlib-only source candidates adapt the Apache-2.0 reference by Joris Roos (original author credits retained). They are not counted as independent proofs and are not imported into `OpenAI086Whole`.

* `source_fidelity/v58/FastFourier.lean`: actual interval integral of integer characters, quadruple expansion and integration over periods 16 and 3, the fourth-moment inequality, quadratic phase invariance of the integrated four-slot form, Parseval and Haar-measure identities, pair-coordinate pushforward of Haar measure, Fourier partial-sum convergence and Bessel bound. The new `v58_slot_partial_fourth` combines the finite fourth moment with Bessel for an arbitrary L² input's truncated Fourier coefficients. No convergence of the randomized Fourier polynomials in the joint random and spatial L⁴ space is asserted. The full short-block lemma, clipping, sampling and burst comparison, mixed maximal estimate, and final summation remain open.
* `source_fidelity/v58/ShortBlockGeometry.lean`: unique dyadic depth-rectangle membership, bounds for the rectangle positions, leaf-mass estimates on real intervals, exact window tiling and K-fold window multiplicity. The designation/disjointness estimate and connection to the actual paper tree still require proof.

Attribution and extraction: `Sec14_2aShortBlockSampling.lean` (lines 30–330, 542–824, 871–1002, 1151–1159, 1169–1173, 1224–1236, selected portions) and `Sec14_2bShortBlockSummation.lean` (lines 28–174 and 319–425, selected portions), from snapshot commit `7b4209609e6a7fb9d9935973ee8541495f943660`. Import changed to `Mathlib`, namespace changed, unused preceding section dependencies removed, and paper-slot Bessel consequence added. The reference license is in `LICENSE-REFERENCE-APACHE2`. Isolated files have 50 theorem declarations, including prerequisites and the new Bessel consequence; this is not 50 newly proved numbered paper lemmas.

## Lemma 9.1 (pp. 81–87)

`external_main_theorem/v58/SparseCount.lean` uses `Auto.sparse_count_explicit` from the pinned reference. All reference geometric assumptions are preserved, corresponding to the paper's five hypotheses, with zero-filled tuples for the absent role, the absolute-value annular test (also implied by a positive signed annular test), and explicit positive R₀. The reserves are fixed at 7,200,000 (d+1)^2 times B and ν. The reference supplies `3·10^11 ℓ L^12 δ^(1/300) M²`; the bridge derives `3·10^11 ℓ L^29 δ^(1/2080) M²` from L≥1 and 0<δ≤1. This is a reference-backed statement candidate, not a reconstruction of the paper's geometric counting proof. Exact type correspondence and kernel replay remain required; independent Lemma 9.1 remains open. The adapted proof is deliberately separate from the original independent proof registry.

## Verification

`bash verify_v58.sh` runs independent import, registry, locked theorem, SHA and source-safety checks, then audits 16 exact declarations in the two isolated adapted files. No Lean/Lake is available in the authoring environment; this script exits 2 and does not certify anything. `python3 external_main_theorem/v58/verify_sparse.py <reference ZIP> --work-dir <empty directory>` builds the pinned dependency and audits the exact sparse theorem's axioms; `--prepare-only` validates snapshot identity and prepares the workspace but explicitly does not certify it. Preparation was tested successfully. The two Python verifiers passed Python syntax compilation. The independent whole-project build and previous V57 candidate proofs still require replay (`bash verify_v57.sh`).

## Remaining obligations

* Lemmas 3.1–3.3, corrected Lemma 3.5, and Lemmas 8.2/8.5/8.6: kernel and statement/application verification.
* Lemma 3.4: exact quantitative compression with the manuscript's dependence on m and D; reference bound differs in m. No claim of closure.
* Lemma 4.3 and Sections 5–6: full analytic chart recurrence, rational splitting, detection, adaptive approximation and localization.
* Theorem 4.7: faithful external LSS inverse theorem; reference's direct finite U³ alternative is not this statement.
* Section 7: joint randomized Fourier limit, remaining sampling, clipping, mixed-norm and short-block estimates.
* Proposition 8.9: concrete graph energy and leakage.
* Lemma 9.1: independent geometric argument remains open; dependency-backed bridge requires verification and fidelity review.
* Sections 9–10: application of sparse counting, analytic complexity, expansion convergence and absorption; Proposition 2.3, Theorem 2.2, Theorem 1.1 independently open.
