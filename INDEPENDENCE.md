# Independent code provenance

All Lean source files under `OpenAI086/` in this ZIP are local original
proof-development artifacts, not copied modules from `lean-trilinearht`.
Only `Mathlib` and `OpenAI086.*` imports are allowed. This is audited by
`tools/static_audit.py`. `tools/review_reference.py` reads the user's
reference ZIP without materializing code into this project.

The baseline already contained partial claims created in earlier work.
This revision adds source files with explicit references to mathematical
ideas; using an idea is not the same as transplanting proof source.

No claim of independent reproof of the 93-page analytic result is made.
