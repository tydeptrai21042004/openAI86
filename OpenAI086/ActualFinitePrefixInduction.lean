import Mathlib
import OpenAI086.ActualDyadicOneLayerPrefix

/-! V18: arbitrary-depth finite-real prefix estimate by row normalization.
No width-tuple decomposition is assumed. The one-layer theorem is applied
successively to genuinely linear, row-dependent compositions.
This is an independent source candidate, pending kernel verification. -/

namespace OpenAI086

/-- Layer zero acts first; layer m is added on the left. -/
def v18PrefixProduct {d : ℕ} (P : ℕ → ℕ → FiniteRealEnd d)
    (n : ℕ) : ℕ → FiniteRealEnd d
  | 0 => LinearMap.id
  | m + 1 => (P m n).comp (v18PrefixProduct P n m)

/-- Exact energy of a scaled family of real linear rows. -/
theorem v18_scale_row_energy {d : ℕ} {Row : Type*} [Fintype Row]
    (a : ℝ) (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (y : Row → Fin d → ℝ) :
    (∑ r : Row, ((a • B r) (y r)) ^ 2) =
      a ^ 2 * (∑ r : Row, (B r (y r)) ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A row-energy bound of a² can be normalized without losing a
factor or requiring all the rows to select the same prefix. -/
theorem v18_normalized_rows {d : ℕ} {Row : Type*} [Fintype Row]
    (a : ℝ) (ha : 0 < a)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ a ^ 2 * finiteRealPair y y) :
    ∀ y : Fin d → ℝ,
      (∑ r : Row, ((a⁻¹ • B r) y) ^ 2) ≤ finiteRealPair y y := by
  intro y
  rw [v18_scale_row_energy a⁻¹ B (fun _ => y)]
  calc
    a⁻¹ ^ 2 * (∑ r : Row, (B r y) ^ 2) ≤
        a⁻¹ ^ 2 * (a ^ 2 * finiteRealPair y y) :=
      mul_le_mul_of_nonneg_left (h y) (sq_nonneg _)
    _ = finiteRealPair y y := by field_simp [ne_of_gt ha] <;> ring

/-- Undo normalization for a family evaluated at different vectors. -/
theorem v18_undo_row_normalization {d : ℕ} {Row : Type*} [Fintype Row]
    (a : ℝ) (ha : 0 < a)
    (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (y : Row → Fin d → ℝ) (E : ℝ)
    (h : (∑ r : Row, ((a⁻¹ • B r) (y r)) ^ 2) ≤ E) :
    (∑ r : Row, (B r (y r)) ^ 2) ≤ a ^ 2 * E := by
  rw [v18_scale_row_energy a⁻¹ B y] at h
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg a)
  have heq : a ^ 2 * (a⁻¹ ^ 2 * (∑ r : Row, (B r (y r)) ^ 2)) =
      ∑ r : Row, (B r (y r)) ^ 2 := by field_simp [ne_of_gt ha] <;> ring
  rwa [heq] at hh

/-- Lemma 3.3, first estimate, for arbitrary m and finite real
scalar rows, with the exact dyadic envelope (k+1)^(2m).
Only within-family nesting is used. -/
theorem v18_actual_finite_prefix_bessel
    {d : ℕ} {Row : Type*} [Fintype Row]
    (P : ℕ → ℕ → FiniteRealEnd d)
    (hsym : ∀ i j u v,
      finiteRealPair (P i j u) v = finiteRealPair u (P i j v))
    (hidemp : ∀ i j u, P i j (P i j u) = P i j u)
    (hnested : ∀ i j u, P i j (P i (j + 1) u) = P i j u)
    (N : Row → ℕ) (k : ℕ) (hN : ∀ r, N r + 1 ≤ 2 ^ k)
    (m : ℕ) (B : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, (B r y) ^ 2) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row, (B r (v18PrefixProduct P (N r) m x)) ^ 2) ≤
      (k + 1 : ℝ) ^ (2 * m) * finiteRealPair x x := by
  induction m generalizing B with
  | zero => simpa [v18PrefixProduct] using hrow x
  | succ m ih =>
      let a : ℝ := (k : ℝ) + 1
      have ha : 0 < a := by dsimp [a]; positivity
      let C : Row → (Fin d → ℝ) →ₗ[ℝ] ℝ :=
        fun r => (B r).comp (P m (N r))
      have hC : ∀ y : Fin d → ℝ,
          (∑ r : Row, (C r y) ^ 2) ≤ a ^ 2 * finiteRealPair y y := by
        intro y
        simpa [C, a, LinearMap.comp_apply] using
          actual_dyadic_one_layer_explicit_log_bound (P m)
            (hsym m) (hidemp m) (hnested m) N k hN B hrow y
      have hnorm := v18_normalized_rows a ha C hC
      have hrec := ih (fun r => a⁻¹ • C r) hnorm
      have hout := v18_undo_row_normalization a ha C
        (fun r => v18PrefixProduct P (N r) m x)
        ((k + 1 : ℝ) ^ (2 * m) * finiteRealPair x x) hrec
      have hp : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [hp, pow_add]
      change (∑ r : Row, (C r (v18PrefixProduct P (N r) m x)) ^ 2) ≤
        (k + 1 : ℝ) ^ (2 * m) * (k + 1 : ℝ) ^ 2 * finiteRealPair x x
      simpa only [a, mul_assoc, mul_left_comm, mul_comm] using hout

/-- The coordinate functional on a real Euclidean coordinate space. -/
def v18CoordinateRow {e : ℕ} (j : Fin e) : (Fin e → ℝ) →ₗ[ℝ] ℝ where
  toFun y := y j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Vector-valued finite-real rows: flatten the row/coordinate pair.
This does not change the logarithmic constant or the row depth. -/
theorem v18_actual_finite_vector_prefix_bessel
    {d e : ℕ} {Row : Type*} [Fintype Row]
    (P : ℕ → ℕ → FiniteRealEnd d)
    (hsym : ∀ i j u v,
      finiteRealPair (P i j u) v = finiteRealPair u (P i j v))
    (hidemp : ∀ i j u, P i j (P i j u) = P i j u)
    (hnested : ∀ i j u, P i j (P i (j + 1) u) = P i j u)
    (N : Row → ℕ) (k : ℕ) (hN : ∀ r, N r + 1 ≤ 2 ^ k)
    (m : ℕ) (B : Row → (Fin d → ℝ) →ₗ[ℝ] (Fin e → ℝ))
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Row, finiteRealPair (B r y) (B r y)) ≤ finiteRealPair y y)
    (x : Fin d → ℝ) :
    (∑ r : Row, finiteRealPair (B r (v18PrefixProduct P (N r) m x))
      (B r (v18PrefixProduct P (N r) m x))) ≤
      (k + 1 : ℝ) ^ (2 * m) * finiteRealPair x x := by
  classical
  let C : Row × Fin e → (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    fun p => (v18CoordinateRow p.2).comp (B p.1)
  have hC : ∀ y : Fin d → ℝ,
      (∑ p : Row × Fin e, (C p y) ^ 2) ≤ finiteRealPair y y := by
    intro y
    simpa [C, Fintype.sum_prod_type, v18CoordinateRow, finiteRealPair, pow_two]
      using hrow y
  have h := v18_actual_finite_prefix_bessel P hsym hidemp hnested
    (fun p : Row × Fin e => N p.1) k (fun p => hN p.1) m C hC x
  simpa [C, Fintype.sum_prod_type, v18CoordinateRow, finiteRealPair, pow_two]
    using h

end OpenAI086
