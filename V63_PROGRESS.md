# V63 continuation — joint actual-path counts and polynomial core estimate

Base: V62. The original paper, pinned external snapshot, locked main statement and independent library are unchanged. All four new declarations are **uncompiled reference-backed candidates**, not independent proofs. No result is marked kernel-certified. The exact manuscript data correspondence is not established.

## New mathematical source

- `external_main_theorem/v63/JointCounts.lean`: `four_joint_count` and `three_joint_count` combine both inequalities in paper Proposition 9.2 (34) for the same concrete reference path, group, modes, tested tuples, and height. The three-core result covers every distinct role pair, including the side role, by defining its mass as the actual sum of `sideWeight`; it uses the upstream core/side incidence bound rather than treating the side as a set of labels. Both use `p0 = 1 - 1/4160`, and `max 1 mult` for the pair-multiplicity coefficient. `M` is any positive common mass upper bound. The original progression-test normalization and proof of the manuscript polynomial parameter reserves are not asserted.
- `external_main_theorem/v63/CorePolynomial.lean`: `core_coefficient_budget` combines the existing schedule bounds for the four-core pattern and all four possible three-core patterns. The bound is `C4c * B^30 * L^4 * K^2 + 4*(C3c * B^30 * IB * L^4 * K^2)`. `leaf_core_polynomial` applies that coefficient directly to the actual retained-cell minimum of the reference's localized patterns, not an arbitrary path-power premise. It uses the reference choices `δs=1/1024`, `J=3`, `Aw=1` and exponent `1/1200`; the numerical error bound `E` is a separate, linear term. The original paper's parameters and geometry must still be related to this reference data, and the absolute error budget must still be established for the printed manuscript.

## Exact theorem clarification

Theorem 4.7 (PDF page 22) is the **discrete** Leng–Sah–Sawhney inverse theorem on `[L]`, with a degree-two filtered nilmanifold, polynomial sequence, rational Malcev basis, dimension and complexity bounds, and Lipschitz test function. The bounded continuous inverse is a subsequent result in Section 4.5. The reference's finite cyclic chart inverse and its continuous inverse are alternative structural results; they do not certify Theorem 4.7 as stated. No new declaration pretends otherwise.

## Outstanding milestones

| Result | V63 status | Exact outstanding task |
|---|---|---|
| Lemma 2.4 | Reference-backed conditional candidate | Independent stopping/lattice correspondence and kernel replay |
| Lemma 3.2 | Joint candidate | Kernel replay and exact analytic statement comparison |
| Lemma 3.3 | Joint candidate | Kernel replay and exact analytic statement comparison |
| Lemma 3.5 | Corrected candidate | Kernel replay and downstream audit; false printed bandwidth term cannot be proved |
| Theorem 4.7 | Exact theorem open | Discrete LSS nilmanifold formulation and proof |
| Section 5 | Reference adaptive construction exists | Exact manuscript correspondence and verification |
| Section 6 | Reference localization construction exists | Exact manuscript correspondence and verification |
| Lemma 8.2 | Reference schedule joint candidate | Original primary/schedule data correspondence and replay |
| Lemma 8.6 | Conditional actual-event bridge | Original event-density budgets and replay |
| Proposition 8.9 | Conditional energy assembly | Original analytic graph/projection hypotheses and replay |
| Proposition 9.2 | Both (34) inequalities jointly on reference data | Printed progression correspondence and parameter reserves; replay |
| Proposition 9.3 | Actual reference leaf estimate with polynomial coefficient | Printed parameter correspondence, absolute error budget, replay |

## Verification

`bash verify_v63.sh --prepare-only --work-dir /tmp/openai086-v63-prep` passed all nine inherited static/model checks and prepared 26 source files. `bash verify_v63.sh --work-dir /tmp/openai086-v63-replay` returned exit 2 (`BLOCKED: Lean/Lake unavailable`). DNS resolution for GitHub failed. No fresh regression cases were invented: the inherited checks are re-run, but cannot substitute for proof elaboration. The new reference dependency `ReferenceV60CorePath` is registered and built before the joint-count candidate is audited. Strict axioms remain enabled by default. Logs: `verification/V63_PREPARATION.json` and `verification/V63_BUILD_ATTEMPT.json`.

The exact whole-paper formalization and independent main proof remain incomplete. A successful selected replay would certify only the elaborated selected declarations, not the mathematical source correspondence.
