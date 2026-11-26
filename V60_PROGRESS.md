# V60 — projection leakage, core path counts, and completion bridges

Base: V59. Same locked original manuscript and theorem. Independent source tree and 59-entry registry unchanged; zero new kernel-certified paper results. Lean/Lake were unavailable during authoring.

## Proposition 8.9 (printed pp. 72–74)

`source_fidelity/v60/ProjectionLeakage.lean` contains seven attributed Mathlib-only proof candidates extracted from `Sec13_3BesselRowsLinearSideEnergy.lean` of the pinned Joris Roos reference (Apache-2.0). In particular:

* `almost_orthogonal_synthesis` and `rows_bessel_of_synthesis` derive the row square-energy bound from the actual complex Hilbert-space pairings and overlap budgets.
* `proj_complement_le` derives the complementary projection bound using the private-coordinate lower bound and pairwise inner-product estimates, rather than assuming a bound for the projection itself.
* `projection_subtotal_close` splits the full coefficient expansion into the selected and complementary labels and bounds the exact subtotal error.
* `subtotals_almost_orthogonal` assembles the component estimates.

The original geometric graph construction and oscillatory pair bounds still require exact statement/data correspondence. The reference `Auto.ActiveSetup.BasicFamilies.FamParams.linear_energy` is audited directly (not counted as a new independent proof).

## Proposition 9.2 (printed pp. 87–88)

`source_fidelity/v60/CoreSummation.lean` contains the attributed actual layer-cake integral argument `distribution_power` and the new specialization `paper_powered_count`: with positive M,B and 0 <= N_s <= M^2, if the sparse mass is bounded by B δ^(1/2080) M^2 for every 0 < δ <= 1, then

    sum_s N_s^(1-1/4160) <= 2 B M^(2-1/2080).

The reference proof of the layer-cake estimate integrates at the threshold (A/K)^(1/c); the original paper uses dyadic bands. This gives the same required powered conclusion by an adapted argument. The proof uses δ=1 to obtain the total mass bound. No new analytic assumptions beyond the stated sparse mass and count bound are needed.

`external_main_theorem/v60/CorePath.lean` invokes the actual reference `four_core_applied_side` and `three_core_applied_side`, retaining their path, representative, anchor, side-incidence, and schedule data. `four_paper_density` and `three_paper_density` weaken the density exponent 1/300 to 1/2080. The two `*_paper_powered` candidates derive the per-scale bound N_s <= M^2 from the reference's total-count theorems and apply the specialized layer-cake bound, using max(1,B) for a positive coefficient. The reference constants and model conventions remain explicit. Full identification of those data and budgets with the manuscript, including the total mass clause of (34) on original data, is not certified.

## Proposition 9.3 / Section 10.2 (pp. 89–91)

`CoreSummation.lean` also extracts the group-product and subadditivity arguments, and adds `paper_min_with_error` to apply the original cell minimum before taking powers of principal terms, keeping the numerical error at power one. The reference final three/four-core estimates are audited directly; this does not establish the exact polynomial budget of (37) on independent manuscript data.

## Proposition 2.3 / Theorem 2.2 (pp. 4–6)

`external_main_theorem/v60/Completion.lean` uses the reference's `activeFinal_holds` and `normalizedAbsorption_of_activeFinal` to obtain a fixed q in (2,3), followed by every positive c and a corresponding nonnegative A uniform in N. `theorem22_strict` retains strict q > 2 (the reference's top-level uniform theorem only states q >= 2), chooses c=1/(2K) where K=(4/3)16^(4/q), and derives C_N <= 2+2KA using `uniform_local_of_normalized`. These are dependency-backed candidates on `Auto.FiniteDepthLocalData` and its admissible kernel class, not independent completions or proofs of exact data correspondence. The reference's adaptive reduction, localization, side estimate, retained estimate and main theorem are additional audit targets, not new proofs. V55 remains the separate exact main-theorem bridge.

## Replay and tests

`bash verify_v60.sh` runs static integrity, registry, locked statement/PDF, independent source safety, 1,201 exact rational special-case regressions, and isolated Lean checks. The tests passed and the script exited 2 at the missing toolchain. The regression tests are not proofs of the real-power or measure-theoretic results.

`python3 external_main_theorem/v60/verify_bridges.py <pinned-reference.zip> --work-dir <empty-dir>` builds the selected reference modules and checks each named declaration's axiom report. `--target CorePath` or `--target Completion` selects one file. `--prepare-only` was tested successfully and never certifies proofs. All new declarations are uncompiled, and syntax/type/statement issues may remain. The verifier audits 32 named targets across the two standalone and two reference-backed files; some targets are existing reference declarations, not new proofs.

Remaining: all kernel replay; exact data/type correspondence across reference proofs; corrected Lemma 3.5 downstream formal audit; Lemma 3.4 averaging; exact LSS theorem 4.7; independent graph/localization/core/absorption proofs and independent main theorem. No status in the independent registry is promoted.
