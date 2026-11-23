import Mathlib
import OpenAI086.ActualDyadicSelectedWidthBessel
import OpenAI086.FiniteDyadicWidthGrouping
import OpenAI086.FiniteAdaptiveRowBessel

/-!
# V17: finite-real variable-prefix estimate for ONE projection family

For genuine nested real orthogonal projections, rows are allowed to
select unrelated prefix depths. The common width grouping is exact;
its single-width row estimate has already been proved without a block
selection premise in `ActualDyadicSelectedWidthBessel`.

The final step is the ordinary finite-level Cauchy--Schwarz inequality.
This is a SOURCE PROOF CANDIDATE until Lean/Mathlib elaboration passes.
It covers m=1 only and does not claim the full Hilbert-space Lemma 3.3.
-/

namespace OpenAI086

/-- The finite type of dyadic block widths admitted by a fixed prefix
budget. There are at most `k+1` different widths. -/
abbrev ActualDyadicWidth (k : ℕ) :=
  {w : ℕ // w ∈ finiteDyadicWidthSet k}

/-- Construct an explicit finite enumeration rather than postulating
finite cardinality of a subtype of `ℕ`. -/
noncomputable def actualDyadicWidthFintype (k : ℕ) :
    Fintype (ActualDyadicWidth k) := by
  classical
  exact Fintype.ofFinset (finiteDyadicWidthSet k).attach (by
    intro w
    simp)

/-- Reindexing the exact prefix sum through attached width labels. -/
theorem actual_dyadic_width_attach_sum {d : ℕ}
    (k : ℕ) (F : ℕ → FiniteRealEnd d) :
    (∑ w ∈ (finiteDyadicWidthSet k).attach, F w.val) =
      ∑ w ∈ finiteDyadicWidthSet k, F w := by
  classical
  simp only [Finset.sum_attach]

/-- Full finite-real one-layer row-prefix bound, with row-dependent
chosen truncation depths. The coefficient is the squared number of
possible dyadic widths; it does NOT depend on the total depth or row
count. Its bound by `(k+1)^2` follows from
`finite_dyadic_width_set_card_le`. -/
theorem actual_dyadic_one_layer_prefix_bessel
    {d : ℕ} {Row : Type*} [Fintype Row]
    (P : ℕ → FiniteRealEnd d)
    (hsym : ∀ j u v,
      finiteRealPair (P j u) v = finiteRealPair u (P j v))
    (hidemp : ∀ j u, P j (P j u) = P j u)
    (hnested : ∀ j u, P j (P (j + 1) u) = P j u)
    (N : Row → ℕ) (k : ℕ)
    (hN : ∀ r, N r + 1 ≤ 2 ^ k)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row, (B r (P (N r) x)) ^ 2) ≤
      ((@Fintype.card (ActualDyadicWidth k)
        (actualDyadicWidthFintype k) : ℝ)) ^ 2 *
        finiteRealPair x x := by
  classical
  letI : Fintype (ActualDyadicWidth k) := actualDyadicWidthFintype k
  let Q : Row → ActualDyadicWidth k → FiniteRealEnd d :=
    fun r w => finiteLinearWidthLevel P k 0 (N r + 1) w.val
  have hprefix (r : Row) :
      (∑ w : ActualDyadicWidth k, Q r w) = P (N r) := by
    have h := finite_linear_prefix_grouped_by_width
      P k (N r) (hN r)
    change (∑ w ∈ (finiteDyadicWidthSet k).attach,
      finiteLinearWidthLevel P k 0 (N r + 1) w.val) = P (N r)
    simpa only [Finset.sum_attach] using h
  have hlevel : ∀ w : ActualDyadicWidth k,
      (∑ r : Row, (B r ((Q r w) x)) ^ 2) ≤
        finiteRealPair x x := by
    intro w
    exact actual_dyadic_selected_width_row_bessel
      P hsym hidemp hnested N k w.val hN B hrow x
  have hsum := finite_level_row_square_bound
    (fun w r => B r ((Q r w) x)) (finiteRealPair x x) hlevel
  have heq (r : Row) :
      B r (P (N r) x) =
        ∑ w : ActualDyadicWidth k, B r ((Q r w) x) := by
    have hr := congrArg (fun L : FiniteRealEnd d => B r (L x)) (hprefix r)
    rw [← hr]
    simp only [LinearMap.sum_apply]
    exact map_sum (B r) (fun w : ActualDyadicWidth k => (Q r w) x) Finset.univ
  calc
    (∑ r : Row, (B r (P (N r) x)) ^ 2) =
      ∑ r : Row, (∑ w : ActualDyadicWidth k,
        B r ((Q r w) x)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [heq r]
    _ ≤ (Fintype.card (ActualDyadicWidth k) : ℝ) ^ 2 *
      finiteRealPair x x := hsum

/-- There are at most `k+1` possible widths. The finite subtype
cardinality has no hidden dependence on the number of selected rows. -/
theorem actual_dyadic_width_card_le (k : ℕ) :
    @Fintype.card (ActualDyadicWidth k) (actualDyadicWidthFintype k) ≤
      k + 1 := by
  change (finiteDyadicWidthSet k).attach.card ≤ k + 1
  simpa only [Finset.card_attach] using finite_dyadic_width_set_card_le k

/-- Explicit logarithmic constant for the complete ONE-LAYER finite
real row-prefix inequality. This matches Lemma 3.3's first estimate
when m=1 and when its Hilbert space is finite-dimensional real.

The paper's m≥2 estimate, square variation and general Hilbert-space
versions remain open in this repository. -/
theorem actual_dyadic_one_layer_explicit_log_bound
    {d : ℕ} {Row : Type*} [Fintype Row]
    (P : ℕ → FiniteRealEnd d)
    (hsym : ∀ j u v,
      finiteRealPair (P j u) v = finiteRealPair u (P j v))
    (hidemp : ∀ j u, P j (P j u) = P j u)
    (hnested : ∀ j u, P j (P (j + 1) u) = P j u)
    (N : Row → ℕ) (k : ℕ)
    (hN : ∀ r, N r + 1 ≤ 2 ^ k)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row, (B r (P (N r) x)) ^ 2) ≤
      (k + 1 : ℝ) ^ 2 * finiteRealPair x x := by
  classical
  letI : Fintype (ActualDyadicWidth k) := actualDyadicWidthFintype k
  have h := actual_dyadic_one_layer_prefix_bessel
    P hsym hidemp hnested N k hN B hrow x
  have hcard :
      (Fintype.card (ActualDyadicWidth k) : ℝ) ≤ k + 1 := by
    exact_mod_cast actual_dyadic_width_card_le k
  have hnonneg : 0 ≤ (Fintype.card (ActualDyadicWidth k) : ℝ) := by
    positivity
  have hcoeff :
      (Fintype.card (ActualDyadicWidth k) : ℝ) ^ 2 ≤
        (k + 1 : ℝ) ^ 2 := by
    nlinarith
  have henergy : 0 ≤ finiteRealPair x x := by
    simp only [finiteRealPair]
    apply Finset.sum_nonneg
    intro i _
    nlinarith [sq_nonneg (x i)]
  calc
    (∑ r : Row, (B r (P (N r) x)) ^ 2) ≤
        (Fintype.card (ActualDyadicWidth k) : ℝ) ^ 2 *
          finiteRealPair x x := h
    _ ≤ (k + 1 : ℝ) ^ 2 * finiteRealPair x x :=
        mul_le_mul_of_nonneg_right hcoeff henergy

end OpenAI086
