# V41 — integrated independent source continuation

**Status: partial source formalization. No successful Lean kernel build in this environment. Theorem 1.1 remains open.**

## Changes
- All 287 independent Lean files are reachable from `OpenAI086Whole`; imports consolidated at the top of `OpenAI086.lean`. Historical adapted modules remain excluded from the independent closure.
- Import lint now detects misplaced imports and cycles in addition to missing modules.
- `PaperV41Section3.lean` combines scalar height covering, occupied bins, exact qualifying-scale finiteness and the infinite tail; gives an explicit bin bound and preserves the counterexample to the original Lemma 3.5(2). These four source declarations (including the conditional main interface below) are not yet kernel checked.
- `PaperV41LocalTargets.lean` introduces actual real-line dyadic grids, normalized interval norms, smooth kernel conditions, maximal operator, local sums and candidate statements for Lemma 2.1 (scalar), Theorem 2.2 and Proposition 2.3. Vector generalization, measurable representatives, optimal-constant properties and integral/measure bridges require completion. These are Prop targets, not proofs.
- `PaperV41MainGoal.lean` preserves the locked main target and adds a combined pointwise estimate and unique bounded extension goal. Its conditional proof depends explicitly on the still-open analytic Schwartz estimate.
- Registry count updated to 287 files and 822 line-anchored theorem declarations; 59 indexed items remain partial, zero certified. Old release docs are retained as historical records.

## Source identity
The supplied `paper(6).pdf` (93 pages, 5 October 2026) has SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`, identical to the existing indexed manuscript. PDF is not redistributed in this ZIP; optional local hash comparison is supported.

## Mathematical correction
Lemma 3.5(2), pp. 13–14: the annulus-width term must be paid for each of at most d separated logarithmic packets. For d=B=2, xi=(1,2^(3L)), r0=alpha=1, beta=2^L, l=1, the scales [-L,0] and [2L,3L] are disjoint and contribute 2L+2 integers. No fixed additive constant plus L+1 bounds this for all L. The corrected bound uses d log_2(2 beta/alpha). Its downstream applications still need audit.

## Verification performed
`verify_v41.sh` passed import, registry, original statement lock, paper hash, lexical safety and all five focused regression suites (27,997 exact model tests), then exited 2 because Lean/Lake are unavailable. Full historical `verify_all.sh` was started but did not finish within the execution limit. No kernel verification is claimed. GitHub was not reachable from the execution environment.

## Remaining obligations (dependency order)
1. Run a pinned Lake build and fix every elaboration failure; review each source candidate for statement fidelity.
2. Certify Section 3: attempt packing, private-coordinate Gram representation, arbitrary nested prefix products, full inherited compression and corrected height lemma, including supremum/vector variants. Propagate erratum downstream.
3. Section 2: complete vector local absolute estimate, maximal stopping construction, uniform-constant reduction and continuous kernel reconstruction.
4. Section 4: quantitative Weyl alternative and chart separation; general quantitative degree-two inverse theorem (external Leng–Sah–Sawhney dependency), continuous transfer, decomposition and detection.
5. Sections 5–6: staggered adaptive approximation, active-cell count, curvature graph/mask localization, filter transfer.
6. Section 7: weighted mixed norm and short-block estimate with exponent tending to zero as q approaches 2; conditional side bound.
7. Section 8: actual component graph and fixed mode expansion, bad-density chain count, separated Bessel rows and square energy with the correct small budget; discharge side hypothesis.
8. Section 9: derive sparse density saving from progression geometry, not from an assumed density bound; complete tuple counts and core power estimate.
9. Section 10: construct retained-cell estimate, choose parameters noncircularly, prove restart and infinite accuracy summation, establish normalized absorption.
10. Prove `V41SchwartzEstimate` from the preceding results, close `V41FullMainGoal`, and prove locked `Theorem1_1_Goal` unconditionally. Require individual statement review, successful kernel compilation and transitive axiom reports for all actual results, plus unnumbered arguments and external dependencies.

## Run
On Ubuntu/WSL with elan installed:

```sh
python3 -m pip install numpy sympy
bash verify_v41.sh
bash verify_paper_complete.sh
```

The first command script is a source/regression audit plus kernel check of selected candidates if the pinned Lean toolchain is available. The second is deliberately fail-closed while the manuscript remains incomplete. `verify_v41.sh` success on another machine would not itself certify the full paper.
