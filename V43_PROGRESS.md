# V43 — Manuscript-level candidates and isolated kernel checks

V43 continues the exact October 5, 2026 paper from V42. This is not a certified release. The independent project has 292 Lean files and 841 theorem declarations by its static inventory. All 59 numbered items remain partial (58 results and Definition 4.1), and the main theorem remains unproved.

## New proofs to check

- `PaperV43Packing.lean`: `v43_sum_generations` partitions a finite set by depth; `v43_lemma31 : V43Lemma31Goal` derives both conclusions of Lemma 3.1 for finite interval-root data using actual Lebesgue interval lengths. Each root is counted once, its parent is in the preceding attempt generation, and the child-length contraction is exactly the input hypothesis of the paper. No bound depends on the finite enumeration horizon. The endpoint-pair model presumes the attempt roots are distinct, as in the finite restart construction; a fidelity review and kernel check remain required.
- `PaperV43Lemma33.lean`: `v43_lemma33` combines the prefix and square-variation estimates for actual nested submodule projections and continuous linear rows, using `Nat.clog 2 (T+1) + 1`. The first m families of a natural-indexed family are used. The finite-family extension and full mathematical fidelity still need review. This theorem relies on existing uncompiled components.
- Corrected Lemma 3.5 scalar assembly is a third isolated check. It is not the full vector/supremum result and does not certify the original false printed statement.

## Actual validation performed here

Static import reachability, registry, original main statement lock, all-59 source inventory and lexical safety passed. Eight Python orchestration tests passed; the tests use mock subprocess responses in temporary directories, not actual Lean runs. `verify_v43.sh` exits 2 with missing Lean/Lake. `certify_complete.py` exits 1 because there is no main proof. The toolchain download was blocked by DNS. No kernel certificate has been generated.

## Run actual Lean checks

On Linux with elan installed:

```bash
bash verify_v43.sh
# or isolate the first manuscript candidate
bash verify_v43.sh --target 3.1
```

Or push the complete project, including `.github/workflows/lean-v43.yml`, to GitHub and run the `Lean manuscript candidate certification` workflow. It installs the pinned toolchain and Mathlib, and runs separate target jobs for 3.1, 3.3 and 3.5-scalar. This workflow was not executed here. Each successful kernel check writes the source hash and actual transitive axiom report; failure cannot produce a PASS. Reports distinguish certification of the encoded statement from human statement-fidelity review. No automatic promotion of the 59-item manuscript registry is performed.

The full main gate now requires both `Theorem1_1_Proved : Theorem1_1_Goal` and `Theorem1_1_Full_Proved : V41FullMainGoal`, with approved foundational axioms only. This makes the unique extension an explicit certification requirement. All other paper obligations and the external inverse theorem remain open.
