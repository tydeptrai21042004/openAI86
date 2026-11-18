> **Whole-project packaging update:** The new `OpenAI086Whole.lean` entrypoint imports the Lemma 3.3 candidate and core together. Theorem 1.1 remains unproved, and kernel compilation has not been confirmed in this environment.

# Proof dependency map: OpenAI #086, October 5, 2026

This dependency map reflects the uploaded paper's organization, not an independent formal proof.

## Target

**Theorem 1.1 (OPEN).** Boundedness of the principal-value trilinear Hilbert transform with shifts \(x-t,x-2t,x-3t\) from \(L^3\times L^3\times L^3\) into \(L^1\).

## Dependency spine from the PDF

```
Theorem 1.1  [UNPROVED]
  └── Lemma 2.4, outer reduction [UNPROVED]
       ├── Theorem 2.2, uniform local estimate [UNPROVED]
       │    └── Proposition 2.3, normalized absorption [UNPROVED]
       │         ├── §3, inherited projections and compression [UNPROVED]
       │         │    ├── Lemma 3.1 scalar packing [finite-model PROVED IN SOURCE]
       │         │    ├── Lemma 3.2 private-coordinate estimates [partial]
       │         │    ├── Lemma 3.3 products of nested prefixes [UNPROVED]
       │         │    └── Lemma 3.4 compression [UNPROVED]
       │         ├── §4, quantitative Weyl alternative/detection [UNPROVED]
       │         ├── §5, predictor replacement [scalar identity only]
       │         ├── §6, quadratic-curvature localization [UNPROVED]
       │         ├── §7, near-band and side-term bounds [UNPROVED]
       │         ├── §8, persistent components and compression [endpoint repair only]
       │         └── §9, density counting and cross-scale concentration [role convention only]
       └── §10, choice of parameters + passage to PV [UNPROVED]
```

## Exact issues to revisit in the PDF before formal development

1. **§5.2 / Lemma 5.3:** For a general augmented input \(F_a\), the predictor moment has an additional private-input coordinate term. The shorter identity in the prose proof requires vanishing of this input coordinate. `ErrataChecks.lean` captures the exact scalar issue; the analytic estimate is not repaired here.
2. **Lemma 8.6:** The hypotheses written for \(i<N\) do not by themselves imply the terminal inclusion \(P_N\subseteq C_N\). `BadDensityChain.lean` checks this set-theoretic dependency but not the quantitative lemma.
3. **§9.1:** A test with first failing role \(j\) has all earlier roles passing, not all later ones. `FirstFailure.lean` verifies a finite three-role analogue, not the complete multi-scale count.

## No implication chain from algebraic resonance to Theorem 1.1

The polynomial identity

\[
- x^2 + 3(x+t)^2 - 3(x+2t)^2 + (x+3t)^2 = 0
\]

is necessary background for phase analysis; it is not sufficient to deduce global \(L^3\to L^1\) boundedness. In particular, the log-divergent elementary bound for finite truncations needs cancellation uniformly in the number of scales. Most of the manuscript's work establishes this quantitative uniformity.

## Next precise independently provable milestones

1. Implement `LocalForm` with measurable kernels and normalized interval integrals.
2. Formalize Lemma 2.1 using the two-coordinate map, change of variables and interpolation/Hölder.
3. Define inherited stopping partitions and prove the complete nested-projection setup.
4. Prove the row-Bessel and binary-prefix estimates of Lemma 3.3.
5. Prove the full quantitative Lemma 3.4 and connect it with the chart estimates of §§4–5.
6. Complete §§6–9 and a proof of Proposition 2.3 with all stopping parameters explicit.
7. Prove Lemma 2.4 including reconstruction of `1/t` and principal-value limits.
8. Only then add `theorem theorem_1_1 : Theorem1_1_Goal := by ...` and verify its axioms.
