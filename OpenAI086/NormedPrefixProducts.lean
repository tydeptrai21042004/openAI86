import Mathlib
import OpenAI086.NormedDyadicPrefix

/-! Dimension-free ordered products. The cumulative family begins at zero,
so its index n+1 is the paper's prefix n. The energy law is proved for
real inner product projections in HilbertPrefixEnergy. -/
namespace OpenAI086

variable {X : Type*} [NormedAddCommGroup X]

def v19PrefixProduct (P : ℕ → ℕ → X →+ X) (n : ℕ) : ℕ → X →+ X
  | 0 => AddMonoidHom.id X
  | m+1 => (P m n).comp (v19PrefixProduct P n m)

/-- Arbitrarily many layers and heterogeneous row codomains. No finite
coordinate representation or commutation across layers is required. -/
theorem v19_normed_product_prefix {R : Type*} [Fintype R]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (P : ℕ → ℕ → X →+ X)
    (hz : ∀ i, P i 0 = 0)
    (henergy : ∀ i a b, a ≤ b → ∀ x,
      ‖P i b x-P i a x‖^2 = ‖P i b x‖^2-‖P i a x‖^2)
    (hcontract : ∀ i n x, ‖P i n x‖^2 ≤ ‖x‖^2)
    (N : R → ℕ) (k : ℕ) (hN : ∀ r, N r ≤ 2^k)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ C*‖x‖^2) (x : X) :
    (∑ r, ‖B r (v19PrefixProduct P (N r) m x)‖^2) ≤
      (k+1 : ℝ)^(2*m)*(C*‖x‖^2) := by
  induction m generalizing B C with
  | zero => simpa [v19PrefixProduct] using hrow x
  | succ m ih =>
    let D : (r : R) → X →+ Y r := fun r => (B r).comp (P m (N r))
    let C' : ℝ := (k+1 : ℝ)^2*C
    have hC' : 0 ≤ C' := by dsimp [C']; positivity
    have hD (y : X) : (∑ r, ‖D r y‖^2) ≤ C'*‖y‖^2 := by
      have h := v19_normed_one_layer (fun n => P m n y)
        (by simp [hz]) (fun a b hab => henergy m a b hab y)
        (‖y‖^2) C (sq_nonneg _) hC (fun n => hcontract m n y) B hrow N k hN
      simpa [D, C', mul_assoc] using h
    have h := ih C' hC' D hD
    have hp : 2*(m+1) = 2*m+2 := by omega
    rw [hp, pow_add]
    simpa [v19PrefixProduct, D, C', mul_assoc] using h

/-- Weighted norm inequality, requiring only the triangle inequality. -/
theorem v19_weighted_norm_add (a : ℝ) (ha : 0 ≤ a) (u v : X) :
    a*‖u+v‖^2 ≤ (a+1)*‖u‖^2+a*(a+1)*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (u+v)) (norm_add_le u v) 2
  calc
    _ ≤ a*(‖u‖+‖v‖)^2 := mul_le_mul_of_nonneg_left h ha
    _ ≤ _ := by nlinarith [sq_nonneg (‖u‖-a*‖v‖)]

/-- The single-family consecutive increment rows form a contraction. -/
theorem v19_increment_rows (Q : ℕ → X →+ X)
    (henergy : ∀ a b, a ≤ b → ∀ x,
      ‖Q b x-Q a x‖^2 = ‖Q b x‖^2-‖Q a x‖^2)
    (hcontract : ∀ n x, ‖Q n x‖^2 ≤ ‖x‖^2)
    (T : ℕ) (x : X) :
    (∑ n : Fin T, ‖Q (n.val+2) x-Q (n.val+1) x‖^2) ≤ ‖x‖^2 := by
  have h := v19_aligned_energy (fun n => Q (n+1) x)
    (fun a b hab => henergy (a+1) (b+1) (Nat.add_le_add_right hab 1) x) 1 T
  have he : (∑ n : Fin T, ‖Q (n.val+2) x-Q (n.val+1) x‖^2) =
      ‖Q (T+1) x‖^2-‖Q 1 x‖^2 := by
    simpa [Fin.sum_univ_eq_sum_range, Nat.add_assoc] using h
  rw [he]
  linarith [hcontract (T+1) x, sq_nonneg ‖Q 1 x‖]

/-- Square variation for m+1 layers, with the exact exponent 2m.
This is the paper's second estimate in the cumulative convention. -/
theorem v19_normed_product_variation
    (P : ℕ → ℕ → X →+ X) (hz : ∀ i, P i 0 = 0)
    (henergy : ∀ i a b, a ≤ b → ∀ x,
      ‖P i b x-P i a x‖^2 = ‖P i b x‖^2-‖P i a x‖^2)
    (hcontract : ∀ i n x, ‖P i n x‖^2 ≤ ‖x‖^2)
    (T k : ℕ) (hT : T+1 ≤ 2^k) (m : ℕ) (x : X) :
    (∑ n : Fin T, ‖v19PrefixProduct P (n.val+2) (m+1) x -
      v19PrefixProduct P (n.val+1) (m+1) x‖^2) ≤
      (m+1 : ℝ)^2*(k+1 : ℝ)^(2*m)*‖x‖^2 := by
  classical
  induction m with
  | zero =>
    simpa [v19PrefixProduct] using
      v19_increment_rows (P 0) (henergy 0) (hcontract 0) T x
  | succ m ih =>
    let a : ℝ := (m:ℝ)+1
    let L : ℝ := (k:ℝ)+1
    let E : ℝ := L^(2*(m+1))*‖x‖^2
    have ha : 0 < a := by dsimp [a]; positivity
    let D : Fin T → X →+ X := fun n => P (m+1) (n.val+2)-P (m+1) (n.val+1)
    let U : Fin T → X := fun n => P (m+1) (n.val+2)
      (v19PrefixProduct P (n.val+2) (m+1) x-v19PrefixProduct P (n.val+1) (m+1) x)
    let V : Fin T → X := fun n => D n (v19PrefixProduct P (n.val+1) (m+1) x)
    have hd (y : X) : (∑ n, ‖D n y‖^2) ≤ (1:ℝ)*‖y‖^2 := by
      simpa [D] using v19_increment_rows (P (m+1)) (henergy (m+1)) (hcontract (m+1)) T y
    have hV : (∑ n, ‖V n‖^2) ≤ E := by
      have h := v19_normed_product_prefix P hz henergy hcontract
        (fun n : Fin T => n.val+1) k (fun n => by have := n.isLt; omega)
        (m+1) 1 (by norm_num) D hd x
      simpa [V,E,L] using h
    have hp : L^(2*m) ≤ L^(2*(m+1)) := by
      have hL : 1 ≤ L := by dsimp [L]; linarith [Nat.cast_nonneg (R := ℝ) k]
      have hL2 : 1 ≤ L^2 := by nlinarith [sq_nonneg (L-1)]
      have he : 2*(m+1) = 2*m+2 := by omega
      rw [he,pow_add]
      simpa using mul_le_mul_of_nonneg_left hL2 (pow_nonneg (by linarith) (2*m))
    have hU : (∑ n, ‖U n‖^2) ≤ a^2*E := by
      calc
        _ ≤ ∑ n : Fin T, ‖v19PrefixProduct P (n.val+2) (m+1) x -
            v19PrefixProduct P (n.val+1) (m+1) x‖^2 :=
          Finset.sum_le_sum (fun n _ => hcontract (m+1) (n.val+2) _)
        _ ≤ a^2*L^(2*m)*‖x‖^2 := by simpa [a,L] using ih
        _ ≤ a^2*E := by
          simpa [E,mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (sq_nonneg a)) (sq_nonneg ‖x‖)
    have he (n : Fin T) : v19PrefixProduct P (n.val+2) (m+2) x -
      v19PrefixProduct P (n.val+1) (m+2) x = U n+V n := by
      simp only [v19PrefixProduct, AddMonoidHom.comp_apply,U,V,D,AddMonoidHom.sub_apply,map_sub]
      abel
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T)))
      (fun n _ => v19_weighted_norm_add a ha.le (U n) (V n))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have hb : a*(∑ n, ‖U n+V n‖^2) ≤ a*((a+1)^2*E) := by
      calc
        _ ≤ (a+1)*(∑ n, ‖U n‖^2)+a*(a+1)*(∑ n, ‖V n‖^2) := hs
        _ ≤ (a+1)*(a^2*E)+a*(a+1)*E :=
          add_le_add (mul_le_mul_of_nonneg_left hU (by positivity))
            (mul_le_mul_of_nonneg_left hV (by positivity))
        _ = _ := by ring
    have hf := (mul_le_mul_left ha).mp hb
    simp_rw [he]
    convert hf using 1 <;> simp [a,E,L,Nat.cast_add,Nat.cast_one] <;> ring

end OpenAI086
