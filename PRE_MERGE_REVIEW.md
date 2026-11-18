# Independent proof development — external Lean review BEFORE integration

Research target: OpenAI #086, *An L³ Bound for the Trilinear Hilbert Transform*,
5 October 2026, slopes `(1,2,3)` only. The 93-page user-supplied PDF is the
mathematical specification; the uploaded `lean-trilinearht-master.zip` is a
**reference for ideas, not a verified replacement for this proof**.

## Independent assessment of the reference ZIP

- The external repository pins Lean `v4.36.0-rc1` and Mathlib revision
  `fbc1661a327737928fe9d69b74f7deaa09eecfbc`, matching the baseline
  project's declared dependencies.
- `TrilinearHT/Auto/Prerequisites/RademacherMenshov.lean` contains theorems
  `nestedProjectionProduct_prefix_rows` and
  `nestedProjectionProduct_successive_jumps`. Mathematical approach:
  *dyadic partition of a varying prefix + Bessel energy + induction in the
  number of noncommuting layers*. This is appropriate for **Lemma 3.3**.
- `TrilinearHT/Auto/Sec04ColumnProjections.lean` contains
  `columnSpatialCompression` and `columnSpatialCompression_complements`.
  It additionally requires local column frames, private coordinates, Gram
  inversion, nested stopping partitions, and quantitative scale control.
  This is appropriate as a *proof design reference*, but wholesale transfer
  would destroy independence and leave a large unaudited dependency graph.
- `TrilinearHT/Theorems.lean` states a Schwartz-space `L³ -> L¹` bound,
  delegated to `Auto.trilinear_ht_bound`. This theorem's statement and
  proof dependencies must be checked with Lean, not simply trusted by name.
- The ZIP has an Apache-2.0 LICENSE. Source code from that ZIP is **not**
  included or imported in this project.
- The read-only source scan finds no `sorry` or `axiom` declarations, but
  this is not conclusive: only successful compilation plus `#print axioms`
  can determine the Lean kernel's assumptions. Source-vs-PDF fidelity must
  also be reviewed, particularly the reported issues in §§5, 8, 9.

Run the repeatable pre-merge review **without copying the code**:

```bash
python3 tools/review_reference.py /path/to/lean-trilinearht-master.zip
```

## Independent integration decisions

| Candidate | Decision | Reason / verification gate |
|---|---|---|
| Ordered-product telescope (Lemma 3.3 algebra) | INTEGRATED IN SOURCE (KERNEL BUILD PENDING) | New independent proof in `NoncommutingProducts.lean`; no commutativity used |
| Product norm error budget | INTEGRATED IN SOURCE (KERNEL BUILD PENDING) | New coarse bound using triangle + submultiplicativity; not a logarithmic bound |
| Pair of noncommuting orthogonal projections | INTEGRATED IN SOURCE (KERNEL BUILD PENDING) | Explicit R² example prevents misidentifying coordinate-mask special case with general Lemma 3.3 |
| Finite prefix split | INTEGRATED IN SOURCE (KERNEL BUILD PENDING) | New combinatorial identity; not the Rademacher–Menshov row inequality |
| Lemma 3.3 arbitrary Hilbert row-Bessel logarithmic inequality | NOT INTEGRATED | Requires independently defined noncommuting nested projections and a dyadic row estimate with Lean proof |
| Lemma 3.4 complete compression | NOT INTEGRATED | Depends on Lemmas 3.2–3.3, measurable cell projections, budgeted stopping and Gram bounds |
| §§4–9 quantitative Weyl/inverse/detection/localization and counting | NOT INTEGRATED | Nontrivial new analytical dependencies; no independently checked proof terms |
| Proposition 2.3, Theorem 2.2, Theorem 1.1 | NOT INTEGRATED | Require all the preceding quantitative analytic bounds and principal-value passage |

## Audit of what is and is not proved

Do not report `lake build` success alone as proving Theorem 1.1: the main
claim is still an unproved proposition. Even the new modules have not yet
been compiled in this execution environment (Lean/Lake unavailable).

Exact requirements before making a **complete formalization** claim:
1. Fully typed main theorem identical in strength to Theorem 1.1 of the PDF.
2. Proof terms for all quantitative hypotheses, with dependencies imported
   **only from Mathlib and independently proved OpenAI086 modules**.
3. Successful reproducible `lake build` under pinned Lean/Mathlib.
4. `#print axioms` on the final theorem (check for unexpected axioms).
5. Explicit mathematical review of the §§5/8/9 corrections and passage to
   principal value; an algebraically verified identity does not fix a missing
   analytic hypothesis.

Nothing from the third-party repository is copied or imported.
