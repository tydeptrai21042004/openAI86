# V13 — Constructed first-entry ranks and a stronger finite Lemma 8.6 bridge

**Source**: `paper(4).pdf`, *An L³ Bound for the Trilinear Hilbert Transform* (5 October 2026), especially the first-entry harmonic counting Lemma 8.5 (PDF page 69–70) and bad-density Lemma 8.6 (PDF page 70).

## Mathematical changes

1. **`ChronologicalFirstEntry.lean`:** Uses the actual minimum membership time of each label (`Nat.find`), breaks same-time ties by label index, constructs a finite chronological prefix, and derives the rank-size inequality from nested-set monotonicity. Proves (as Lean proof candidates) positive, bounded, and injective chronological ranks, including a map `Fin M → Fin M`.
2. **`ChronologicalIncidence.lean`:** Derives the exception-fraction estimate directly from these canonical ranks, rather than assuming that the labels' original `Fin M` indices already have first-entry order.
3. **`ChronologicalHarmonic.lean`:** Constructs an equivalence from the injective finite rank-index map and reindexes the reciprocal ranks to the ordinary harmonic sum `H_M`. It states a finite-chain first-entry incidence theorem with a coverage hypothesis.
4. **`FiniteChronologicalChain.lean`:** Eliminates that coverage hypothesis: extend any finite nested set chain with the full universe only *after* its last observed step. This establishes an arbitrary finite-chain form of Lemma 8.5, assuming only a monotone chain and a per-label exception multiplicity bound.
5. **`ConcreteChronologicalLogChain.lean`:** Applies the finite counting result twice, with **independent chronological orders** across heights and positions, uses the actual union exceptional predicate and base-1.1 integer log rank, and derives position monotonicity from the interleaved `P ⊆ C ⊆ P_next` conditions. No V12-style first-entry rank-size hypotheses are present. It retains bad-height density and quantitative absorption assumptions; it is not the full manuscript Lemma 8.6.
6. **`InitialBadHeightCount.lean`:** Exactly counts the original lemma's automatically bad initial heights `h < Δ` by `min(J, Δ)` and proves a nonnegative lower bound. The initial segment is **not yet integrated** into the shifted-window bound above.

## Verification status (critical)

The proofs are candidate Lean 4 source, **not yet accepted by a Lean kernel**: `lake` and `lean` are unavailable in this environment, and attempts to access Lean download servers fail DNS resolution. Any compilation/elaboration issues must be fixed on Ubuntu/WSL with the pinned toolchain. The source audits check imports, the 59-goal inventory, and the absence of prohibited placeholders; they do **not** typecheck the proof terms.

`tools/test_v13_chronological_rank.py` performs 272,692 exact small-instance checks including adversarial non-native label orders, equal arrival times, labels that never appear during the test window, fractional exceptional densities, harmonic reindexing, and the initial-bad-height count.

`./verify_smoke_v13.sh` also reruns V9–V12 and errata regressions. Exit 2 after all source/numeric tests means no Lean kernel build occurred.

## Remaining proof obligations

- **Kernel build:** compile every new module using pinned Lean and Mathlib; resolve any elaboration errors. No manuscript theorem can be certified without this.
- **Lemma 8.6:** integrate initial bad heights into the full `J+1` statement, match strict versus non-strict inequalities and the full quantitative `Q`/`N` statement, check zero-cardinality versus the PDF's nonempty-set hypothesis, and prove all parameters/side conditions in downstream applications.
- **Lemma 3.3:** obtain full arbitrary-Hilbert logarithmic row-prefix and noncommuting-product variation estimates. The finite/partial bridges do not imply this.
- **Lemma 3.4 and Sections 4–10:** the compression, continuous inverse theory, localization, side energy, sparse count, uniform absorption, and Theorem 1.1 remain independently open. The manuscript's 59-result catalog stays at 21 partial/38 finite proxies/0 fully kernel-verified.

## Run

```bash
unzip openAI86_V13_Independent_Continuation_FULL.zip
cd openAI86-main
bash verify_smoke_v13.sh
```

No external Lean code from the published parallel formalization has been copied.
