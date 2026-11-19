# Independence guarantee (source provenance, NOT theorem certification)

`OpenAI086` imports only Mathlib and its own modules. All newer seven modules are original source written for this project. `OpenAI086Whole.lean` imports only `OpenAI086`. The older Apache-2.0 adaptation of the published Rademacher–Menshov code and the dependent Theorem 1.1 bridge were intentionally omitted from this ZIP.

The named source paper supplies the mathematical ideas and target results. Those are not third-party Lean proof dependencies.

`tools/check_project_integrity.py` and `tools/lean_source_safety.py` check source-level evidence of import independence and placeholder absence; neither constitutes verification by the Lean kernel. The full theorem remains open.
