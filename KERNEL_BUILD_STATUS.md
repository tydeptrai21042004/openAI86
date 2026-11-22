# Kernel build status — V5 (2026-11-22)

**Not compiled in this runtime**: `lean`/`lake` are unavailable; no kernel
proof is being claimed. Static integrity and V5 exact-arithmetic tests pass,
but the full historical regression suite was not completed within the
execution window. The V5 archive has **77 Lean files** and **210 source
`theorem` declarations**; 17 of 59 paper results have partial work, zero
have complete kernel certificates. See `verify_smoke_v5.sh` for a fast
fail-closed check and `verification/V5_RELEASE_AUDIT.json` for details.

---

# Kernel build status — V3 (2026-11-22)

**Not checked by the Lean kernel in this environment.** All static imports,
source safety checks and Python regressions passed; `bash verify_all.sh`
exited **2** because `lake` is unavailable. The exact current counts are:
**71 Lean files**, **193 theorem declarations**, **59 indexed paper results**,
**17 partial** and **0 fully kernel certified**.

The six new V3 modules contain candidate proofs of finite real
Gram/projection and multilevel Bessel estimates and common-neighbor/four-step
walk identities. They have not been compiled here. The full Lemmas 3.2, 3.3,
3.4, 9.1 and Theorem 1.1 remain open in the repository.

## Historical status entries (V1/V2)

# Kernel build status — 22 November 2026

**Not verified in the authoring runtime.** Lean, Lake, and Elan were absent;
DNS access to the Lean release server was unavailable. `bash verify_all.sh`
passed its Python tests and returned exit code **2**, exactly as intended
when no Lean kernel build was possible. This is not a successful proof build.

- Static module-import reachability: **65/65** Lean files reachable.
- Safety scan: **PASS**, no unacknowledged `sorry`/`axiom` declarations.
- Registry: **59** numbered paper results; **17** with partial Lean work;
  **0** with complete kernel certificates.
- Module-source theorem declarations: **172** (small intermediate statements,
  not paper-level formalizations).
- Main Theorem 1.1: **unproved**.

When available, run `bash verify_all.sh` on Ubuntu/WSL, or use the included
GitHub Actions workflow. Check that `lake build OpenAI086Whole` succeeds,
then review the `#print axioms` output. A successful build only certifies
the precise imported source declarations, not the unproved main theorem.


### Further v2 candidate revision

Five imported modules were added after the earlier status entry. The
source count is now **65 Lean files** and **168 theorem declarations**.
All source checks and 6151 new regressions pass; a kernel build is **still
not available** and theorem-level certification is unchanged.
