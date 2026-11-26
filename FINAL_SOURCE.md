# V61 continuation — consolidated Lean source

V61 adds seven uncompiled proof candidates in four new Lean files, a targeted axiom replay for existing and reference-backed milestones, a strict axiom policy switch, and exact finite regression models. See `V61_PROGRESS.md` for the current scope and blockers. The V60 description below remains historical; none of the independent registry entries has been promoted.

## V60 base description

This package is a consolidation of the V52 GitHub snapshot and all cumulative V53–V60 changes. It is not a claim that the entire paper has been formalized. No new mathematical proof is asserted by this packaging step. All V60 proof candidates remain subject to Lean kernel checking and source-fidelity review.

## Source layout

- `OpenAI086.lean`, `OpenAI086Whole.lean`, `OpenAI086/`: independent Mathlib-only partial formalization (329 files in the independent audit, 991 line-anchored theorem declarations). The independent goal remains open.
- `source_fidelity/`: attributed standalone adaptations and auxiliary proof candidates.
- `external_main_theorem/v55`, `v58`, `v59`, `v60`: pinned-reference bridges for the main theorem, compression, Weyl splitting, short-block comparison, sparse counting, core paths and normalized absorption.
- `final_source/FinalMain.lean`: exports `OpenAI086.Final.theorem1_1` and `OpenAI086.Final.theorem1_1_full` from the existing V55 proof-transfer candidates. These declarations require the prepared workspace; the file is not a self-contained proof.
- `reference_snapshot/lean-trilinearht.zip`: exact user-supplied Joris Roos reference snapshot, commit `7b4209609e6a7fb9d9935973ee8541495f943660`, with its original license and attribution intact. The reference uses an adapted mathematical argument, not an exact formalization of all numbered statements.
- `paper(7).pdf`: original manuscript, SHA-256 `24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936`.
- `verification/`: registry, proof traceability, fidelity notes and source checks. The 59-entry inventory includes a definition; it is not a completion count.

## Replay on Ubuntu / WSL

Install Elan, Python 3 and Git, and ensure `lean` and `lake` are on PATH. The project pins Lean `leanprover/lean4:v4.36.0-rc1` and Mathlib commit `fbc1661a327737928fe9d69b74f7deaa09eecfbc`. The pinned reference's Lake manifest is preserved in the prepared workspace. Network access or pre-existing dependencies are required for the Lake/Mathlib cache.

To check only the main theorem bridges first:

```bash
bash verify_final.sh --main-only --work-dir /tmp/openai086-main-check
```

To replay the full selected source suite, including the independent build and standalone adaptations:

```bash
bash verify_final.sh --work-dir /tmp/openai086-all-check
```

To extract the pinned source and prepare the workspace without running Lean:

```bash
bash verify_final.sh --prepare-only --work-dir /tmp/openai086-source
```

The workspace must be new or empty. `--no-cache` skips the Mathlib cache fetch if you have arranged dependencies yourself. The runner preserves the exact paper and target hashes, checks static integrity, builds the reference first, then attempts the exact and full main-target bridges and the selected lemma candidates. It records outputs under the workspace, including `final_verification.json`, and rejects missing or unexpected axiom reports. A successful selected-target replay would not certify all original manuscript statements. No independent theorem status is promoted by this runner.

## Remaining work

- All kernel builds and declaration-level axiom checks need replay. The packaging environment has no Lean or Lake.
- The original Lemma 3.5(2) requires a dimension-dependent bandwidth correction; downstream formal audit is incomplete.
- The reference's alternative finite inverse theorem is not the exact LSS nilmanifold theorem (Theorem 4.7).
- Full exact correspondence of the original interval, projection, graph, chart and core data to the adapted proof remains open, including the finite-measure averaging clause of Lemma 3.4.
- Independent analytic Sections 5–10 and the independent main theorem remain incomplete.

See `V60_PROGRESS.md`, `verification/V56_PAPER_FIDELITY.md`, `verification/V57_PAPER_FIDELITY.md` and `verification/PAPER_RESULTS_INDEX.json` for the current candidate inventory and historical source-fidelity audits.
