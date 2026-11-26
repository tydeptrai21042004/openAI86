# V74 — paper-specific fixed-stack integration

Source-only continuation from V73. The module `external_main_theorem/v74/PaperFixedStacks.lean` adapts the reference Section 14.5b side estimate to V73 paper-specific rolling states and block sums, including all cell-depth and block-ancestor packing arguments. It does not change the pinned reference or the independent library.

- `paperToLeaf` and `paperToLeafQ` provide the actual generic `SideLeafM` record, including the state decomposition and range proof required by the fixed-stack estimate.
- `paper_basic_side_energy` and `paper_block_energy` instantiate the V73 rolling estimates on certified cells and their block ancestors respectively. The first pays K, the second does not.
- `paper_side_estimate` supplies those energy bounds and the unchanged variation/augmented-U arguments to `leaf_side_estimateM`. It exports the common cut, clipped two-side and three-side bounds, and retained path cap. It still assumes the global linear-side bound, pair-smallness, helper/far tests, normalized input bounds, and numerical stack reserves on the actual data.
- `paperToLeaf_sv_physical`, `paperToLeafQ_sv_physical`, and `paper_restored_eq` link those augmented inputs to the V72 physical local form. The U slot is not incorrectly identified with its physical projection as a vector; only its local-form value agrees.

Remaining: construct the hypotheses on original attempts (including far/helper tests and weighted maximal theorem), exact first tops, progression/torus/Fourier counts, parameter selection, and exact LSS inverse theorem. Sections 2–6 remain incomplete as previously documented; Lemma 3.5(2) requires its correction. No Lean compilation, numerical regression, or verification runner executed; all new proofs are candidates. The new module is included in the optional verification runner for the user's later use.
