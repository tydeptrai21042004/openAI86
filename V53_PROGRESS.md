# V53 — source-level continuation of OpenAI086

Source: `paper(7).pdf`, October 5, 2026, 93 pages. SHA-256
`24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`.
The original Theorem 1.1 statement lock is unchanged. No external formalization was imported.

## New proof candidates (11 declarations)

- `PaperV53ParameterCompletion.lean` (Section 10.3, p.92): monotonicity for small positive bases; actual integer ceiling `P = ceil(eta^(-alpha))`; ceiling power estimate without `hPpower`; main power reduction; side cost with `K+2 <= C0*P^C5` and `C5*beta <= 1/8` rather than `K+2 <= P`; inverse quarter-power estimate.
- `PaperV53SparseExponent.lean` (Lemma 9.1, p.87): auxiliary choices `alpha=delta^(1/1040)`, `kappa=alpha*alpha`, exact three exponents, reduction to `delta^(1/2080)` and the remaining-density case. The preceding geometric mass inequality is still a hypothesis; the finite geometric lemma itself is NOT proved.
- `PaperV53WeylIntegral.lean` (Lemma 4.3, p.17): actual Bochner integral perturbation estimate from an integrable pointwise modulation identity, followed by iterative sample propagation. The chart-specific translation identity, change of variables for the Fourier transform, and analytic error bound are still required.

Two existing V52 proof scripts have algebraic-normalization edits (parameter-order division and six-pair multiplication). Their statements are unchanged. These edits have not been compiler-confirmed.

## Verification

Run `OPENAI086_PAPER=/path/to/paper.pdf bash verify_v53.sh` from the repository root. The new verifier builds the whole independent library, checks 17 named constants (11 new and 6 pre-existing candidates), captures exact `#print axioms` output, and checks the axiom allowlist. Even a successful component check does not automatically mark any paper-level lemma complete. The source PDF can be checked by path or by its current filename; the full distribution includes the PDF.

Results in this environment: all static checks passed; exact PDF hash matched; 1,600 new exact arithmetic models and 3,000 V52 models passed; 10 parser tests passed. No Lean/Lake installation was available and downloading the pinned toolchain failed due to DNS/network restrictions. The V53 verifier exited 2 (blocked). All new Lean declarations are uncompiled proof candidates. No paper result was promoted to kernel-verified. The independent registry records 59 entries (58 numbered mathematical results and one definition), all partial. Main theorem remains open.

## Remaining proof obligations (not waived)

1. Compile and repair the whole dependency closure; check statement fidelity of the existing candidates for Lemmas 3.1, 3.5 and 8.5 before certifying them. The printed Lemma 3.5(2) misses a dimension multiplier on the width term; preserve the counterexample, prove the corrected statement and audit its downstream uses.
2. Section 2: actual change of variables and local interpolation, maximal-function stopping reduction, admissible kernel decomposition and passage to the principal value.
3. Section 3: finish actual measurable nested column projections, representative energy, anchor transitions, restarts, and compression, rather than replacing those with assumptions.
4. Section 4: derive the chart-specific Fourier recurrence and error, transference and rational subspace bounds, Fourier expansion and continuous inverse/detection. Theorem 4.7 is an external theorem in the source paper; a conditional formalization needs an exact external statement, and an unconditional one needs its proof or a certified import.
5. Sections 5–6: staggered adaptive approximants, delayed fit predictor moments, curvature graphs/colors and masks, all quantitative localization errors.
6. Sections 7–8: actual randomization fourth moment, depth block comparison, common cuts, complete graph constructions, Bessel and projection leakage estimates.
7. Section 9: actual greedy counting blocks, difference covers, minimal-growth and slab-cover argument, geometric mass inequality on p.87, all applications to core tuples and powered estimate. V53 addresses only the final exponent arithmetic.
8. Section 10: prove analytic complexity hierarchy and overhead bounds, derive the retained-cell estimate and full restart construction; use accuracy summation to finish Proposition 2.3 and then Lemma 2.4 and Theorem 1.1.

The remaining obligations are not claims of mathematical counterexamples (except the documented printed height-count inequality). This continuation does not constitute full formalization of the paper.
