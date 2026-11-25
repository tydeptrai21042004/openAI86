## V27 current status — 24 November 2026

253 reachable Lean files; 654 theorem declarations; 58 partial source entries, 1 open entry with proxy and domain definitions, 0 fully kernel-certified. 11,082 exact model checks passed. Theorem 4.7, uniform L³ estimate and Lean kernel verification remain open. See `V27_PROGRESS.md` and `bash verify_smoke_v27.sh`. Older statuses below are historical.

## V26 current status — 24 November 2026

245 reachable Lean files; 636 theorem declarations; 51 partial source entries, 8 proxy-only, 0 fully kernel-certified. 9,883 exact model checks passed. New direct components for 4.6, 4.10, 4.11, 4.12, 5.4, 5.6, 5.8, 6.3, 7.4. Lean/Lake unavailable; Theorem 1.1 and 4.7 remain open. See `V26_PROGRESS.md` and `bash verify_smoke_v26.sh`. Older statuses below are historical.

## V25 current status — 24 November 2026

237 reachable Lean files; 611 public theorem declarations; 42 partial source entries, 17 proxy-only entries, 0 kernel-certified paper results. New: 9,901 exact model checks; V23–V25 total: 62,743. Paired Schwartz principal-value integral, spatial L1 majorant and concrete trilinear operator are uncompiled source candidates. The uniform L3 estimate and external inverse theorem remain open. See V25_PROGRESS.md and `bash verify_smoke_v25.sh`. Lean/Lake unavailable here; no kernel certification. Historical statuses follow.

## V21 current status — 24 November 2026

203 reachable Lean files; 467 theorem declarations; 30 partial source items, 29 proxy-only items, 0 fully kernel-verified paper results. 37,002 new exact model/parser checks passed. Lean/Lake unavailable. See V21_PROGRESS.md, `bash verify_lemma33_v21.sh` and `bash verify_smoke_v21.sh`.

Historical content follows.

# Build and certification status — continuation

- Source integrity, all imported local modules: **PASS** (38 Lean files).
- Source safety (no forbidden proof placeholders or non-Mathlib formalization import): **PASS**.
- Static source declarations counted: **95 theorems**; this does not mean that they compile.
- Python symbolic and numerical checks: **PASS**. They are not formal proofs.
- `bash verify_all.sh`: **exit 2** — `lake` absent, no Lean kernel build executed.
- `python tools/paper_obligation_report.py --require-complete`: **exit 3** — missing independent full-paper proofs.
- Named results with partial code: **17 of 59**; fully kernel-certified named results: **0 of 59**.
- Main theorem: **OPEN**. No proof term supplied for `OpenAI086.Theorem1_1_Goal`.

On a Linux machine with Lean installed: `lake exe cache get && bash verify_all.sh`.
The proof remains incomplete even if the available intermediate source builds.

## V48 continuation

V48 adds the pointwise private-column transition lower bound, a conditional simultaneous half-contraction theorem for restart measure and representative energy, and finite measurable nested history-labelled anchor partitions. It records 2,012 exact finite-model regressions. Static import/registry/source-safety checks pass for 308 reachable modules and 924 theorem declarations. Lean/Lake are unavailable; target checks are blocked and no manuscript result is promoted to kernel-certified. See `V48_PROGRESS.md` and `V48_VERIFICATION_LOG.txt`.
