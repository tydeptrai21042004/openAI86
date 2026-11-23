# V14 — Full-height finite Lemma 8.6 counting and dyadic level assembly

**Source:** `paper(4).pdf` (5 October 2026), especially Lemma 8.6 on PDF page 70, Lemma 8.5 on pages 69–70, and the binary-prefix estimate of Lemma 3.3 on pages 8–9.

## New independently developed Lean source **candidates**

1. `InitialHeightAbsorption.lean` — proves the *scalar quantitative absorption* in the original full `H+lag` height window, preserving the cost of the first `lag` automatically bad heights. Includes both nonstrict and strict variants. Mathematically, with `N+1` positions, per-position post-lag cost `Q`, per-height cost `R`, `2(lag+Q) ≤ δ(H+lag)`, and sufficient bad incidences at each position, it yields `N+1 ≤ 2R/δ` (or strict `<` for strict density).
2. `FullChronologicalBadDensity.lean` — uses exact integer-arithmetic `11/10` cardinality bins, nested `Finset` lists, and *constructed* chronological first-entry ranks in both height and position directions. The first `lag` heights are included in the quantitative budget; includes the terminal inclusion `P_N ⊆ C_N` missing from the published text.
3. `FullChronologicalBadDensityStrict.lean` — retains the paper's **strict** bad-height density and final **strict** chain-length inequality. No abstract assumed exceptional-fraction budget; both come from the existing `finite_chronological_harmonic_density` theorem candidate.
4. `FullBadHeightReindex.lean` — formally states the exact identity `sum_(h<lag) 1 + sum_post = lag + sum_post`, defines the actual original full-window bad-height predicate, and connects that predicate to the two full-window chain statements.
5. `FiniteLevelEnergyAssembly.lean` — proves a scalar `L² E` squared-energy assembly across `L` binary-block levels, plus a version for real-linear row operators. This is a linear-row version of the Rademacher–Menshov *assembly* sublemma already present in finite scalar form for Lemma 3.3, **not** the projection-specific block-Bessel bound or the full logarithmic noncommuting-prefix estimate.

6. `FiniteDyadicDistinctLengths.lean` — proves the binary prefix constructor selects **at most one block of each length** (a property stronger than its known count bound), that every width is a power of two, and that a dyadically aligned prefix yields aligned blocks. Also proves different starts on the same aligned grid are separated by at least one width. This supplies missing **combinatorial structure** for the projection-specific Bessel step of Lemma 3.3; that step itself is not yet proved.

## What was tested

- `python3 tools/test_v14_full_height.py` — **471,877** exact Fraction/integer cases, including 328,310 original-window/bad-density checks, 45,000 level-assembly tests, 24,642 dyadic size/partition checks, 73,686 alignment/grid-separation tests, sharp examples, and 225 empty/zero-index boundary checks.
- The actual finite label sets are monotone in height and satisfy `P_i,h ⊆ C_i,h ⊆ P_(i+1),h`. Both exception multiplicities, their harmonic cost, the union-based bad-height predicate, and strict-vs-nonstrict final bounds are checked.
- `tools/check_project_integrity.py`, `tools/check_registry_integrity.py`, `tools/check_all_59_lean_targets.py`, and `tools/lean_source_safety.py` check packaging, status bookkeeping and prohibited placeholder terms.
- A successful **Lean/Lake kernel build was NOT possible in the execution environment**; the executable is absent and downloading it fails at DNS resolution. Consequently none of the new Lean proofs may be reported as kernel-certified, and proof elaboration bugs are possible.

## Remaining exact gaps

- Typecheck and repair **all** V9–V14 candidates with the repository-pinned Lean/Mathlib toolchain. The source checks and numerical model checks do not imply successful elaboration.
- **Lemma 3.3**: obtain the uniform blockwise Bessel/row bounds for all independent dyadic *block lengths*, and prove the `m`-factor noncommuting projection product with exact manuscript logarithmic constant. The new level-assembly lemma is only the last scalar step after those hypotheses.
- **Lemma 8.6**: although the finite set counting skeleton now matches the full height convention, the manuscript uses a quantified `HM` (harmonic number), `L=floor(log_1.1 M)` and exceptional/nonempty hypotheses in its actual PRE graph application; this implementation is a finite-universe rational-bin version and its exact use in the full analytic chain has not been shown.
- **Lemmas 3.4, 5.3, Sections 4–10, Proposition 2.3 and Theorem 1.1** remain independently open. Manuscript inventory: 59 indexed, 21 partially modeled, 38 finite proxies, **0 fully kernel-certified**.

## Run on Ubuntu or WSL

```bash
unzip openAI86_V14_Independent_Continuation_FULL.zip
cd openAI86-main
bash verify_smoke_v14.sh
```

Exit code `2` means source/numerical checks ran but no Lean kernel build happened. A successful `lake build OpenAI086Whole` and axiom inspection are prerequisites for any kernel-certification claim.

No code from the parallel public Lean formalization has been imported or copied.
