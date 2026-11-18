# Code provenance and license

This increment is a reviewed *code adaptation*, not an independently
authored proof. To avoid misrepresenting the level of independence, it is
separated in `OpenAI086/Lemma33Reviewed.lean`.

Original source: Joris Roos, `lean-trilinearht`,
`TrilinearHT/Auto/Prerequisites/RademacherMenshov.lean`,
Apache License 2.0. Original source credited authors to Codex.

Full original reference is **not** shipped or imported.
The mathematical statements and proof structure originate from that reference;
renaming the Lean namespace and bundling the proof locally does **not** make
this original proof authorship.

- Reference SHA-256: `77ae6d6d4678f68e3568fcc64eafbc30ac3214b5f4b394e5a9b5c7e9f30a7676`
- Adaptation: retain only the finite Rademacher--Menshov row estimates,
  nested projection product and successive jump proof; change namespace
  to avoid collision with the independent original code.
- No declarations named `axiom`, `sorry`, `admit` in the module.
- Run a real `lake build` and inspect `#print axioms` before any
  certification. This environment cannot run Lean.

Because the supplied source is Apache-2.0, license and notice are included
with the distribution.
