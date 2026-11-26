# V68 — Interval variation, fixed stacks and general polylogarithmic overhead

Continues V67. This is a source-only delivery. The five new theorem declarations have not been elaborated or kernel checked; no Lean compilation or numerical regression tests were run. The original paper and reference are preserved.

## Added proofs

- `depth_interval_coloring`: greedy induction on a finite index set, removing a latest-starting interval. All remaining overlapping neighbors contain the depth r(a)+1. Their number is at most m-1; choose an unused color in Fin m. Empty increments may have any color. Counts repeated intervals through their distinct indices.
- `variation_of_overlap`: inserts the coloring into actual ActiveSetup.VarCap certified-cell variation, assigning zero-length increments and empty endpoint sets to the unused colors. This supplies the bounded-overlap step of Lemma 7.3 given the reference variation capacity and an overlap cap. The case m=0 is not included (m can be replaced by max 1 m); crossing the start of an attempt still needs the original zero-history correspondence.
- `fixed_stack_common_reserve`: applies the actual FamParams.stackEA_le, collecting variation costs, frozen-base energies, prefix jump constants, binary depth and configuration count into H. Gives stackEA <= (P+2)*35*H^6*|R| and untouched energy <=35*H^6*|R|. The H bounds are hypotheses, not new analytic estimates. This is a bound on the reference stack energy envelope used in Lemma 7.4; exact paper stacks and their energy hypotheses remain to be matched.
- `eventually_log_power_le` and `eventually_ceiling_overhead`: general fixed logarithmic degree d, rather than only d=2, with eta=exp(-k^theta) and P=ceil(eta^(-alpha)). Eventually exp(C*(1+log(2k))^d) <= P^(1/8). This completes the scalar domination step of Section 10.3 at source-candidate level. It does not establish that every analytic overhead satisfies the assumed polylog bound.

## Remaining source work

- Section 2: exact local admissible kernels and outer reduction correspondence.
- Section 3: compression statement and corrected-height downstream correspondence.
- Section 4: exact LSS Theorem 4.7, pooled Fourier tails and chart correspondence.
- Section 5: delayed high fits, adaptive schedules and restart data.
- Section 6: original graph, mask, helper-filter and catalog correspondence.
- Section 7: exact weighted mixed-norm theorem (Lemma 7.1), exact basic-output variation capacity and endpoint conventions, actual stack hypotheses and near-band correspondence.
- Section 8: original geometric data and all graph energy hypotheses.
- Section 9: original progression parameters and numerical error correspondence.
- Section 10: prove actual overhead bounds and integrate original parameter choices and summation.

The reference-backed main proof candidate is unchanged. Full exact-paper source and independent proof are incomplete. This release must not be labeled certified or fully formalized.
