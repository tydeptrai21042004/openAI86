# V61 continuation: explicit outer reduction, corrected heights, graph chains, core sum

Base: user-supplied V60 archive. The exact PDF, reference snapshot, locked theorem, independent source tree and 59-entry registry are unchanged. All seven new Lean declarations are uncompiled candidates. The original Lemma 3.5(2) is false as printed (V42 counterexample); therefore a 100% proof of the original uncorrected statements is not possible. The correction must remain explicit. The paper's Theorem 4.7 is the **discrete** Leng–Sah–Sawhney nilmanifold theorem, not the subsequent continuous chart inverse lemma. The reference uses a different finite inverse theorem and supplies a continuous chart inverse theorem, which is useful but is not the exact LSS result.

## New Lean source

- `source_fidelity/v61/IndependentMilestones.lean`: `corrected_height_count` combines the complete qualifying-set enumeration and explicit width bound, obtaining `d * (8*(d+1)^2*log₂(2B) + log₂(β/α) + 1)` for all positive integral scaling powers. `absorb_uniform` gives the exact scalar absorption step. Axiom replay targets include existing joint candidates `v56_lemma32` and `v43_lemma33`, actual height values, exceptional blocks and event energy. This file imports only the independent source tree, but is outside its historical inventory.
- `external_main_theorem/v61/GraphChain.lean`: `primary_inclusion` derives PRE primary inclusion in CURRENT at every event including the terminal one from `ModeComponents.E_le_F` and the image map. `floorlog_component_chain` supplies this inclusion, nonemptiness and both height-monotonicity conditions to the corrected printed floor-log lemma. It still requires the temporal link, label count, multiplicities, floor-log bad-height and budget hypotheses. The reference uses a 9/10 ratio test; full predicate and actual-event identification are not established.
- `external_main_theorem/v61/OuterAndStages.lean`: `outer_uniform` and `outer_main` implement the two conditional implications of Lemma 2.4 on the pinned reference's concrete local data, retaining strict q > 2. They do not use the already-proved main theorem to prove intermediate statements. The audit also includes the actual reference adaptive reduction, localization, continuous inverse, height stabilization, side energy, and leaf core estimate. The independent local-kernel and lattice correspondence is still open.
- `source_fidelity/v61/WeightedCore.lean`: `weighted_core_min` applies the original cell clipping to each finite set of principal terms, aggregates the path-power budget and keeps numerical errors linear. The upstream path-power and error bounds remain hypotheses, not proved by this final assembly.

## Twelve unfinished milestones (no kernel promotions)

| Paper | V61 evidence | Remaining |
|---|---|---|
| Lemma 2.4 | Both conditional implications on reference data; scalar absorption candidate | Independent stopping, kernel and lattice correspondence |
| Lemma 3.2 | Existing joint actual L² candidate selected for named axiom audit | Kernel replay; exact source correspondence |
| Lemma 3.3 | Existing joint nested-product candidate selected for named axiom audit | Kernel replay; exact source correspondence |
| Lemma 3.5 | Explicit corrected full qualifying-set count | Audit all downstream uses of corrected bound; kernel replay |
| Theorem 4.7 | Reference continuous inverse audit and alternative finite inverse retained | Exact discrete LSS nilmanifold theorem not formalized |
| Section 5 | Actual reference adaptive reduction selected for audit | Original staged fit and delayed projection data correspondence |
| Section 6 | Actual reference attempt localization selected for audit | Original graph and catalog data correspondence |
| Lemma 8.2 | Actual rational packet candidate and tiny-span candidates retained | Connect to actual primary schedule and tiny space; kernel replay |
| Lemma 8.6 | Terminal inclusion and monotonicity supplied on reference graph components | Actual event linkage and floor-log predicate hypotheses; kernel replay |
| Proposition 8.9 | Actual reference linear energy and independent event assembly selected for audit | Original graph and leakage correspondence |
| Proposition 9.2 | V60 three/four-core powered path bridges retained | Actual progression tests and original budgets |
| Proposition 9.3 | Weighted minimum/power assembly and actual reference leaf core estimate audit | Derive the paper's path-power and error budgets and uniform polynomial dependence |

## Replay

`bash verify_v61.sh --prepare-only --work-dir /tmp/openai086-v61-prep` prepares the pinned workspace and validates static integrity. To replay all selected declarations (requires Elan and dependency access):

```bash
bash verify_v61.sh --strict-axioms --work-dir /tmp/openai086-v61-check
```

`--strict-axioms` rejects all dependencies except `propext`, `Classical.choice`, `Quot.sound`; the older compatibility policy permits `Lean.ofReduceBool`. The runner builds the two adapted helper libraries before compiling their importing V61 files and builds the named independent dependencies before the independent milestone audit. It does not certify exact whole-paper fidelity even after a successful replay.

The environment had no `lean`, `lake`, or `elan` and DNS resolution of github.com failed. Actual preparation and all seven static/regression checks passed; Lean kernel replay is blocked. Regression models are not proofs. No new result has been marked verified. See `verification/V61_PREPARATION.json` and `verification/V61_BUILD_ATTEMPT.json`.
