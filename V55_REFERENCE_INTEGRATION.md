# V55: Reference-backed replay (not an independent proof)

The user-supplied archive `lean-trilinearht-master(2).zip` identifies commit
`7b4209609e6a7fb9d9935973ee8541495f943660` in its ZIP comment. Its archive
SHA-256, Lean v4.36.0-rc1, and Mathlib revision are checked by the new script.
The source is attributed to Joris Roos and contributors, Apache-2.0; its LICENSE
and source headers are retained in the isolated replay workspace. No upstream
proofs are copied into the independent OpenAI086 source tree by this patch.

## Run

Unzip the changes into V54. Keep the original reference archive available.

```bash
python3 external_main_theorem/v55/verify_snapshot.py /path/to/lean-trilinearht-master\(2\).zip --work-dir /tmp/v55-reference --prepare-only
python3 external_main_theorem/v55/verify_snapshot.py /path/to/lean-trilinearht-master\(2\).zip --work-dir /tmp/v55-reference-build --exact-only
python3 external_main_theorem/v55/verify_snapshot.py /path/to/lean-trilinearht-master\(2\).zip --work-dir /tmp/v55-reference-full
```

Use a new empty work directory for each run. The exact-only route checks the
locked pointwise PV and seminorm goal. The full route additionally builds the
local V41 operator dependencies and checks the exact unique-extension goal.
If those unverified local candidates fail to compile, the exact certificate
remains separate. `reference_certificate.json` records which stage succeeded;
only actual successful elaboration and accepted axiom reports set flags true.
No independent status or strict certification gate is altered.

## Crosswalk for future independent work

| Paper obligation | Reference source under TrilinearHT/Auto | Candidate to inspect |
|---|---|---|
| 3.1 packing | Sec04ColumnProjections, Prerequisites/DyadicStopping | completedColumnAttempts_packing |
| 3.2 projection | Sec04ColumnProjections | cellProjectionCoefficients_normal |
| 3.3 nested prefixes | Prerequisites/RademacherMenshov | nestedProjectionProduct_prefix_rows, nestedProjectionProduct_jump_rows_of_bessel |
| 3.4 compression | Sec04ColumnProjections | columnSpatialCompression, columnSpatialCompression_complements |
| 3.5 height correction | Prerequisites/RationalLinearAlgebra | rational_dyadic_scale_count (dimension-dependent bandwidth cost) |
| 4.3 Weyl | Sec09_1ReturnWeylSplitting; Prerequisites/LatticeTransference | weylSplitting |
| 4.7 substitute | Sec07FiniteInverse, Sec08ContinuousDecomposition | finite_inverse, continuous_inverse; not the general nilmanifold theorem |
| 5 base | Sec11_1a through Sec11_2c | activeCellReduction |
| 6 localization | Sec12_1 through Sec12_4 | attempt_localization |
| 7 short blocks | Sec14_2a, Sec14_2b, Sec14_5b | short_block_comparison, side_estimate_leaf |
| 8 graphs/energy | Sec13_1 through Sec13_5 | linear_energy, first_top_count_main (within their enclosing namespaces) |
| 9.1 sparse mass | Sec15_3FiniteSparseCountLemma | sparse_count_explicit |
| 9 core | Sec15_4 and Sec15_5 | frequency hypothesis checks and final sums |
| 10.3, 10.4 | Sec16_1 through Sec16_3 | retainedMin_holds, activeFinal_holds |
| 2.3 | Sec16_3SummingUpdateLevels | normalizedAbsorption_of_activeFinal activeFinal_holds |
| 2.2 | same | uniform_of_activeFinal activeFinal_holds (q >= 2 in exported statement) |
| 1.1 | same | tht_main, trilinear_ht_bound, tendsto_T_trunc, T_trunc_eq_neg |

The reference blueprint changes some intermediate statements. For example, its
finite inverse result replaces the imported LSS theorem, and its height bound
contains dimension-dependent bandwidth cost. This table maps relevant mathematical
ideas, not exact statement equivalences. A successful external main certificate
would not certify all 58 original intermediate statements.

## Checks in current environment

The archive preparation succeeds and validates the original target SHA. The
reference source has complete-looking theorem bodies and the README reports
registration in Palomar, but no Lean or Lake is available here. Both new Lean
bridges are uncompiled proof candidates. The independent proof is still open.
