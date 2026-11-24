import Mathlib
import OpenAI086.HilbertPrefixEnergy

/-! Exact finite-horizon bridge: append a zero before the paper's P₀,
and repeat P_T beyond T. This does not impose extra projection assumptions
on the original finite family. -/
namespace OpenAI086
open scoped RealInnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Finite index obtained by clamping to the final generation. -/
def v19Clamp (T n : ℕ) : Fin (T+1) := ⟨min n T, by have := Nat.min_le_right n T; omega⟩

def v19Augment {T : ℕ} (P : ℕ → Fin (T+1) → X →+ X) (i : ℕ) : ℕ → X →+ X
  | 0 => 0
  | n+1 => P i (v19Clamp T n)

theorem v19_clamp_original {T : ℕ} (n : Fin (T+1)) : v19Clamp T n.val = n := by
  apply Fin.ext
  have h : n.val ≤ T := by have := n.isLt; omega
  simp [v19Clamp, Nat.min_eq_left h]

theorem v19_augment_sym {T : ℕ} (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, ⟪P i n u,v⟫_ℝ = ⟪u,P i n v⟫_ℝ) :
    ∀ i n u v, ⟪v19Augment P i n u,v⟫_ℝ = ⟪u,v19Augment P i n v⟫_ℝ := by
  intro i n u v
  cases n with
  | zero => simp [v19Augment]
  | succ n => exact hs i (v19Clamp T n) u v

theorem v19_augment_idem {T : ℕ} (P : ℕ → Fin (T+1) → X →+ X)
    (hi : ∀ i n x, P i n (P i n x) = P i n x) :
    ∀ i n x, v19Augment P i n (v19Augment P i n x) = v19Augment P i n x := by
  intro i n x
  cases n with
  | zero => simp [v19Augment]
  | succ n => exact hi i (v19Clamp T n) x

theorem v19_augment_nested {T : ℕ} (P : ℕ → Fin (T+1) → X →+ X)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x) :
    ∀ i a b, a ≤ b → ∀ x, v19Augment P i a (v19Augment P i b x) = v19Augment P i a x := by
  intro i a b hab x
  cases a with
  | zero => simp [v19Augment]
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      have h : v19Clamp T a ≤ v19Clamp T b := by
        change min a T ≤ min b T
        exact min_le_min (by omega) le_rfl
      exact hn i _ _ h x

/-- Actual ordered finite family, with index n exactly as in the paper. -/
def v19FiniteProduct {T : ℕ} (P : ℕ → Fin (T+1) → X →+ X) (n : Fin (T+1)) : ℕ → X →+ X
  | 0 => AddMonoidHom.id X
  | m+1 => (P m n).comp (v19FiniteProduct P n m)

theorem v19_augmented_product_eq {T : ℕ} (P : ℕ → Fin (T+1) → X →+ X)
    (n : Fin (T+1)) (m : ℕ) :
    v19PrefixProduct (v19Augment P) (n.val+1) m = v19FiniteProduct P n m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [v19PrefixProduct,v19FiniteProduct,v19Augment,v19_clamp_original,ih]

/-- Lemma 3.3 first estimate, finite horizon and arbitrary real Hilbert
space, in squared form. k can be any binary envelope exponent. -/
theorem v19_finite_horizon_prefix {T k m : ℕ} (hT : T+1 ≤ 2^k)
    {R : Type*} [Fintype R] {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, ⟪P i n u,v⟫_ℝ = ⟪u,P i n v⟫_ℝ)
    (hi : ∀ i n x, P i n (P i n x) = P i n x)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x)
    (N : R → Fin (T+1)) (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2) (x : X) :
    (∑ r, ‖B r (v19FiniteProduct P (N r) m x)‖^2) ≤
      (k+1 : ℝ)^(2*m)*‖x‖^2 := by
  have h := v19_real_hilbert_prefix (v19Augment P) (fun _ => rfl)
    (v19_augment_sym P hs) (v19_augment_idem P hi) (v19_augment_nested P hn)
    (fun r => (N r).val+1) k (fun r => by have := (N r).isLt; omega) m B hrow x
  simpa only [v19_augmented_product_eq] using h

/-- The square-variation estimate, finite horizon and nonempty product. -/
theorem v19_finite_horizon_variation {T k m : ℕ} (hT : T+1 ≤ 2^k)
    (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, ⟪P i n u,v⟫_ℝ = ⟪u,P i n v⟫_ℝ)
    (hi : ∀ i n x, P i n (P i n x) = P i n x)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x) (x : X) :
    (∑ n : Fin T, ‖v19FiniteProduct P n.succ (m+1) x -
      v19FiniteProduct P n.castSucc (m+1) x‖^2) ≤
      (m+1 : ℝ)^2*(k+1 : ℝ)^(2*m)*‖x‖^2 := by
  have h := v19_real_hilbert_variation (v19Augment P) (fun _ => rfl)
    (v19_augment_sym P hs) (v19_augment_idem P hi) (v19_augment_nested P hn) T k hT m x
  have he (n : Fin T) : v19PrefixProduct (v19Augment P) (n.val+2) (m+1) =
      v19FiniteProduct P n.succ (m+1) := by
    simpa [Nat.add_assoc] using v19_augmented_product_eq P n.succ (m+1)
  have he' (n : Fin T) : v19PrefixProduct (v19Augment P) (n.val+1) (m+1) =
      v19FiniteProduct P n.castSucc (m+1) := by
    simpa using v19_augmented_product_eq P n.castSucc (m+1)
  simpa only [he,he'] using h

end OpenAI086
