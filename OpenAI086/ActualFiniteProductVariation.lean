import Mathlib
import OpenAI086.ActualFinitePrefixInduction

/-! V18: finite-real square variation for arbitrary ordered projection
products. Inductively split the newest outer layer and use weighted
Cauchy–Schwarz, preserving the paper's m² L^(2(m-1)) constant.
This is a source candidate, not a kernel certificate. -/
namespace OpenAI086

private theorem v18_energy_nonneg {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ finiteRealPair x x := by
  unfold finiteRealPair
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- Weighted two-vector Cauchy–Schwarz, with the denominator cleared. -/
theorem v18_weighted_pair_add {d : ℕ} (u v : Fin d → ℝ)
    (a : ℝ) (ha : 0 ≤ a) :
    a * finiteRealPair (u+v) (u+v) ≤
      (a+1)*finiteRealPair u u + a*(a+1)*finiteRealPair v v := by
  unfold finiteRealPair
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (u i - a*v i)]

/-- Square variation of a nonempty ordered product, with T consecutive
increments. The m+1-layer formulation avoids natural subtraction at m=0. -/
theorem v18_actual_finite_product_variation_succ {d : ℕ}
    (P : ℕ → ℕ → FiniteRealEnd d)
    (hsym : ∀ i j u v,
      finiteRealPair (P i j u) v = finiteRealPair u (P i j v))
    (hidemp : ∀ i j u, P i j (P i j u) = P i j u)
    (hnested : ∀ i j u, P i j (P i (j+1) u) = P i j u)
    (T k : ℕ) (hT : T+1 ≤ 2^k) (m : ℕ) (x : Fin d → ℝ) :
    (∑ n : Fin T, finiteRealPair
      (v18PrefixProduct P (n.val+1) (m+1) x - v18PrefixProduct P n.val (m+1) x)
      (v18PrefixProduct P (n.val+1) (m+1) x - v18PrefixProduct P n.val (m+1) x)) ≤
      (m+1 : ℝ)^2 * (k+1 : ℝ)^(2*m) * finiteRealPair x x := by
  classical
  induction m with
  | zero =>
      have h := nested_projection_square_variation_bound
        (fun n y => P 0 n y) (hsym 0) (hidemp 0) (hnested 0) x T
      simpa [v18PrefixProduct, Fin.sum_univ_eq_sum_range] using h
  | succ m ih =>
      let a : ℝ := (m : ℝ)+1
      let L : ℝ := (k : ℝ)+1
      let E : ℝ := L^(2*(m+1)) * finiteRealPair x x
      have ha : 0 < a := by dsimp [a]; positivity
      have hL : 1 ≤ L := by dsimp [L]; linarith [Nat.cast_nonneg (R := ℝ) k]
      have hE : 0 ≤ E := by
        exact mul_nonneg (pow_nonneg (by linarith) _) (v18_energy_nonneg x)
      let A : Fin T → Fin d → ℝ := fun n =>
        P (m+1) (n.val+1)
          (v18PrefixProduct P (n.val+1) (m+1) x - v18PrefixProduct P n.val (m+1) x)
      let D : Fin T → FiniteRealEnd d := fun n => P (m+1) (n.val+1) - P (m+1) n.val
      let B : Fin T → Fin d → ℝ := fun n => D n (v18PrefixProduct P n.val (m+1) x)
      have hrow : ∀ y : Fin d → ℝ,
          (∑ n : Fin T, finiteRealPair (D n y) (D n y)) ≤ finiteRealPair y y := by
        intro y
        have h := nested_projection_square_variation_bound
          (fun n z => P (m+1) n z) (hsym (m+1)) (hidemp (m+1)) (hnested (m+1)) y T
        simpa [D, LinearMap.sub_apply, Fin.sum_univ_eq_sum_range] using h
      have hB : (∑ n : Fin T, finiteRealPair (B n) (B n)) ≤ E := by
        have h := v18_actual_finite_vector_prefix_bessel P hsym hidemp hnested
          (fun n : Fin T => n.val) k (fun n => by have := n.isLt; omega)
          (m+1) D hrow x
        simpa [B, E, L] using h
      have hp : L^(2*m) ≤ L^(2*(m+1)) := by
        have hpow : 1 ≤ L^2 := by nlinarith [sq_nonneg (L-1)]
        have hnon : 0 ≤ L^(2*m) := pow_nonneg (by linarith) _
        have he : 2*(m+1) = 2*m+2 := by omega
        rw [he, pow_add]
        simpa using mul_le_mul_of_nonneg_left hpow hnon
      have hA : (∑ n : Fin T, finiteRealPair (A n) (A n)) ≤ a^2*E := by
        calc
          (∑ n : Fin T, finiteRealPair (A n) (A n)) ≤
              ∑ n : Fin T, finiteRealPair
                (v18PrefixProduct P (n.val+1) (m+1) x - v18PrefixProduct P n.val (m+1) x)
                (v18PrefixProduct P (n.val+1) (m+1) x - v18PrefixProduct P n.val (m+1) x) := by
                apply Finset.sum_le_sum
                intro n _
                exact nested_projection_single_energy (fun j y => P (m+1) j y)
                  (hsym (m+1)) (hidemp (m+1)) (n.val+1) _
          _ ≤ a^2*L^(2*m)*finiteRealPair x x := by simpa [a,L] using ih
          _ ≤ a^2*E := by
            have h := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp (sq_nonneg a)) (v18_energy_nonneg x)
            simpa [E, mul_assoc] using h
      have heq (n : Fin T) :
          v18PrefixProduct P (n.val+1) (m+2) x - v18PrefixProduct P n.val (m+2) x = A n+B n := by
        simp only [v18PrefixProduct, LinearMap.comp_apply, A, B, D, LinearMap.sub_apply, map_sub]
        abel
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T)))
        (fun n _ => v18_weighted_pair_add (A n) (B n) a ha.le)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
      have hbound : a * (∑ n : Fin T, finiteRealPair (A n+B n) (A n+B n)) ≤
          a*((a+1)^2*E) := by
        calc
          _ ≤ (a+1)*(∑ n : Fin T, finiteRealPair (A n) (A n)) +
              a*(a+1)*(∑ n : Fin T, finiteRealPair (B n) (B n)) := hsum
          _ ≤ (a+1)*(a^2*E) + a*(a+1)*E :=
              add_le_add (mul_le_mul_of_nonneg_left hA (by linarith))
                (mul_le_mul_of_nonneg_left hB (by positivity))
          _ = a*((a+1)^2*E) := by ring
      have hfinal := (mul_le_mul_left ha).mp hbound
      simp_rw [heq]
      convert hfinal using 1 <;> simp [a,E,L, Nat.cast_add, Nat.cast_one] <;> ring

end OpenAI086
