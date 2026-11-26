# V62 continuation — actual schedule and event links, leaf budgets

Base: V61 full archive. This release keeps the original 93-page PDF, locked main theorem, pinned reference archive and historical independent inventory unchanged. New declarations are in the attributed reference/source-fidelity tracks, outside the historical independent library inventory. No kernel certification is claimed. In particular the full exact paper, and the independent main proof, remain incomplete. Literal fidelity to the false printed Lemma 3.5(2) is impossible; keep its corrected statement.

## New proof candidates (8 declarations)

- `external_main_theorem/v62/ExceptionalSchedule.lean`: `exceptional_schedule` proves both conclusions of Lemma 8.2 on the actual reference schedule, with the exceptional set defined by filtering path indices. It applies the reference packet count to get `4*dmax`, and derives the tiny rational space closure from `gap_of_not_exceptionalAt`, `tinySpan_small`, and `tiny_of_mem_tinySpan`. Assumes the actual valid schedule and packet-width hypothesis; no independent proof or exact manuscript data correspondence claimed.
- `external_main_theorem/v62/EventChains.lean`: `linked_event_floorlog` constructs temporal label inclusion via `ModeSystem.link_labels` from genuine geometric link witnesses (nested pre-cells, separated block starts and shared/adjacent mode representatives). It also derives same-event inclusion including the terminal event and both height monotonicities. `floorlog_ne_of_ratio` proves failure of the reference's nine-tenths size test implies distinct floor logs for positive sizes. `bad_fraction_of_ratio` proves the 1/10 bad-density implication provided the exceptional/height-bad sets cover all nongood primaries. The converse size implication is false; the remaining task is deriving multiplicity and density hypotheses for the actual event family and assembling the printed chain application.
- `source_fidelity/v62/PathCore.lean`: `leaf_weighted_sum`, `leaf_budget`, `core_from_leaf_budgets` transfer the finite path power and numerical-error budgets into weighted cell bounds. The exact finite Tonelli identity uses leaf weights; errors are summed linearly and the full cell contribution is clipped before subadditivity. The original analytic path budget and actual spatial leaf representation still need proof.
- `source_fidelity/v62/SideEnergy.lean`: `side_energy_from_normalized_errors` derives global squared leakage from a normalized local error, a finite leaf representation and the pathwise event count. Combines this with existing projected-row and colour-energy bounds. The full graph-colouring, oscillatory leakage and Bessel estimates still need exact paper correspondence.

## Milestones (all candidates remain uncompiled)

| Result | V62 change | Still required |
|---|---|---|
| Lemma 2.4 | Retained V61 reference conditional reductions | Independent local data and lattice correspondence |
| Lemma 3.2 | Retained joint candidate | Kernel replay and fidelity |
| Lemma 3.3 | Retained joint candidate | Kernel replay and fidelity |
| Lemma 3.5 | Retained corrected dimension-dependent count | Downstream audit and kernel replay |
| Theorem 4.7 | No new inverse theorem | Exact external LSS nilmanifold theorem; V51 interface is abstract, not a proof |
| Section 5 | Retained reference adaptive reduction | Staged-fit and delayed-projection correspondence |
| Section 6 | Retained reference localization | Graph and catalog correspondence |
| Lemma 8.2 | Joint two-clause actual schedule candidate | Kernel replay and original schedule/primary data correspondence |
| Lemma 8.6 | Actual geometric link implication; ratio comparison | Derive actual event multiplicities and density hypotheses; integrate comparisons |
| Proposition 8.9 | Normalized leakage-to-global-energy assembly | Verify projection, graph, packing and almost-orthogonality hypotheses |
| Proposition 9.2 | Retained V60 powered count bridges | Original progression tests and uniform budgets |
| Proposition 9.3 | Leaf path-to-cell budget and clipped core assembly | Analytic amplitude/frequency and path-power bounds |

## Replay and tests

`bash verify_v62.sh --prepare-only --work-dir /tmp/openai086-v62-prep` verifies static preparation. `bash verify_v62.sh --work-dir /tmp/openai086-v62-replay` builds and audits all selected declarations; strict axioms are enabled by default. Existing work directories are refused. `--main-only` limits kernel replay to the main theorem bridges, but static preparation remains comprehensive. The new adapted dependencies are registered as Lake libraries.

The preparation ran successfully. 84,140 new exact finite regression cases passed; 9 static checks passed; 24 selected source files prepared. Actual kernel replay stopped with exit code 2: Lean and Lake unavailable. DNS access to github.com also failed in the environment. The regression models are not proofs. The two JSON reports contain the actual preparation and blocked-build results. No new proof has been kernel-verified. Even a successful selected-target replay does not certify exact original paper fidelity.
