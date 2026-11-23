# V16 — common-width dyadic-prefix bridge for Lemma 3.3

## Mathematical changes

New modules:

1. `OpenAI086/FiniteDyadicWidthGrouping.lean`:
   - `grouped_linear_list_sum`: exactly regroup a list of linear maps by a finite set of numerical labels.
   - `finite_dyadic_width_mem_set`: every binary-prefix block width belongs to a common, row-independent `finiteDyadicWidthSet k`.
   - `finite_dyadic_width_set_card_le`: this common width set contains at most `k+1` possible widths.
   - `finite_linear_prefix_grouped_by_width`: **unconditional operator identity** expressing `P N` as a sum of width-grouped dyadic increments; it incorporates the essential initial increment `Δ₀ = P₀`.
   - `finite_dyadic_linear_pairs_widths_nodup`: no width occurs twice in a given prefix.
   - `finite_linear_width_level_zero_or_aligned_block`: each row-width contribution is **zero or one** grid-aligned increment block. It is not an arbitrary sum of equal-width blocks.
2. `OpenAI086/FiniteDyadicOrderedWidthExpansion.lean`:
   - `finite_ordered_product_expansion_on_widths`: distributivity through arbitrary **ordered noncommuting** linear-map products over a finite width set.
   - `finite_ordered_actual_prefix_width_expansion`: exact grouped expansion for independently chosen truncation depths in distinct layers.
   - `finite_row_actual_prefix_width_expansion`: exact grouped expansion for different prefix choices in different rows, with no common depth assumption.
   - `finite_linear_row_actual_prefix_width_expansion`: applying a genuine linear row functional preserves this algebraic identity.

3. `OpenAI086/ActualDyadicMaskedLevelSum.lean`:
   - `masked_finite_row_contraction`: setting any subset of rows to zero preserves the row contraction bound.
   - `actual_dyadic_masked_tuple_bessel`: an ordered noncommuting product of actual projection-difference blocks has sharp Bessel constant one even when arbitrary rows are masked off.
   - `actual_dyadic_masked_multilevel_bessel`: masks depending on both the row and width tuple preserve the `K²` level-sum bound.
4. `OpenAI086/FiniteDyadicRowBlockSelection.lean`:
   - `finite_dyadic_row_width_choices_exist`: derives row-indexed active flags and aligned block indices with no additional representation assumption.
   - `finite_dyadic_row_paper_block_choices_exist`: identifies every selected group with an actual zero-prepended projection increment, uniformly in the test vector.
   - `finite_dyadic_multilayer_row_choices_exist`: simultaneously extracts selections for all layers and rows.

This makes the **algebraic common-width prefix decomposition unconditional**. Unlike the V15 `actual_dyadic_linear_row_prefix_reduction`, the V16 width-expansion statements do not take an `hdecomp` hypothesis. No commutativity or analytic Bessel estimate is assumed.

## What is still open

The V16 nested width sums must still be flattened into a single finite **tuple of common widths**, one width per projection layer. V16 now has the precise zero-or-one block extraction and masked Bessel bound, but must convert Nat-valued aligned positions into one uniformly bounded `Fin count` choice family and prove the masking/product identity at each width tuple. Then the `(k+1)^m` tuple count should yield `(k+1)^{2m}` squared-energy control for the row-prefix theorem. The squared-variation bound, arbitrary Hilbert-space generalization, Lemma 3.4, and Sections 4–10 remain open.

Do not claim that `Lemma 3.3`, `Lemma 3.4` or `Theorem 1.1` is already proved. The V16 results are source proof candidates until Lean kernel compilation succeeds.

## Verification and installation

`tools/test_v16_width_grouping.py` passes 16,868 exact checks and uses exact `fractions.Fraction` arithmetic, noncommuting rational projection matrices, `P₀ ≠ 0`, variable row/layer depths, ordered products of up to four layers, and full width-tuple expansion examples. These checks **are not a Lean proof**.

Run:

```bash
bash verify_smoke_v16.sh
```

- Exit `0`: source checks, exact models **and** the actual pinned Lean build and entrypoint elaboration succeeded. This verifies the encoded theorem statements, *not the full article*.
- Exit `2`: source/model checks succeeded but `lean`/`lake` unavailable; **no kernel certificate**.
- Any other nonzero exit: regression, audit, toolchain, or elaboration/build failure.

Set `V16_EXTENDED=1` to include the slower unchanged V15 exact-rational regression before attempting the Lean build.

For a fresh Mathlib checkout, set `LEAN_V16_DOWNLOAD_CACHE=1` to run `lake exe cache get` before building. The pinned toolchain is in `lean-toolchain`.

## Independence and provenance

This code is an independent continuation of `openAI86_V15_Independent_Continuation_FULL.zip`. It references the uploaded 93-page paper for mathematics and does not copy another project's Lean proof. `verification/reference_only` is excluded from the import graph.
