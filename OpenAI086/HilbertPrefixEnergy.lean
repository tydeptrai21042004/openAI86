import Mathlib
import OpenAI086.NormedPrefixProducts

/-! Real Hilbert-space specialization of the dimension-free prefix machinery.
A complex Hilbert space may be viewed as a real inner product space, but
its realification bridge and finite-chain packaging still require checking. -/
namespace OpenAI086

open scoped RealInnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The exact Pythagorean energy law follows from self-adjointness,
idempotence and nesting. No coordinate model or finite dimension is used. -/
theorem v19_real_projection_energy (Q : ℕ → X →+ X)
    (hsym : ∀ n u v, ⟪Q n u,v⟫_ℝ = ⟪u,Q n v⟫_ℝ)
    (hid : ∀ n x, Q n (Q n x) = Q n x)
    (hnest : ∀ a b, a ≤ b → ∀ x, Q a (Q b x) = Q a x)
    (a b : ℕ) (hab : a ≤ b) (x : X) :
    ‖Q b x-Q a x‖^2 = ‖Q b x‖^2-‖Q a x‖^2 := by
  have hself : ⟪Q a x,Q a x⟫_ℝ = ⟪x,Q a x⟫_ℝ := by
    rw [hsym a x (Q a x), hid a x]
  have hcross : ⟪Q a x,Q b x⟫_ℝ = ‖Q a x‖^2 := by
    rw [hsym a x (Q b x), hnest a b hab x, ← hself, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, real_inner_comm (Q b x) (Q a x), hcross]
  ring

/-- Orthogonal projections are contractions, directly from Pythagoras. -/
theorem v19_real_projection_contract (Q : X →+ X)
    (hsym : ∀ u v, ⟪Q u,v⟫_ℝ = ⟪u,Q v⟫_ℝ)
    (hid : ∀ x, Q (Q x) = Q x) (x : X) : ‖Q x‖^2 ≤ ‖x‖^2 := by
  have hcross : ⟪x,Q x⟫_ℝ = ‖Q x‖^2 := by
    calc
      _ = ⟪x,Q (Q x)⟫_ℝ := by rw [hid]
      _ = ⟪Q x,Q x⟫_ℝ := (hsym x (Q x)).symm
      _ = _ := real_inner_self_eq_norm_sq _
  have h := norm_sub_sq_real x (Q x)
  rw [hcross] at h
  nlinarith [sq_nonneg ‖x-Q x‖]

/-- Real Hilbert prefix inequality for arbitrary products, given a
zero-augmented nested family. The finite-chain extension is separate. -/
theorem v19_real_hilbert_prefix {R : Type*} [Fintype R]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (P : ℕ → ℕ → X →+ X) (hz : ∀ i, P i 0 = 0)
    (hsym : ∀ i n u v, ⟪P i n u,v⟫_ℝ = ⟪u,P i n v⟫_ℝ)
    (hid : ∀ i n x, P i n (P i n x) = P i n x)
    (hnest : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x)
    (N : R → ℕ) (k : ℕ) (hN : ∀ r, N r ≤ 2^k) (m : ℕ)
    (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2) (x : X) :
    (∑ r, ‖B r (v19PrefixProduct P (N r) m x)‖^2) ≤
      (k+1 : ℝ)^(2*m)*‖x‖^2 := by
  have h := v19_normed_product_prefix P hz
    (fun i => v19_real_projection_energy (P i) (hsym i) (hid i) (hnest i))
    (fun i n => v19_real_projection_contract (P i n) (hsym i n) (hid i n))
    N k hN m 1 (by norm_num) B (by simpa using hrow) x
  simpa using h

/-- Real Hilbert-space square variation with the same paper constant. -/
theorem v19_real_hilbert_variation
    (P : ℕ → ℕ → X →+ X) (hz : ∀ i, P i 0 = 0)
    (hsym : ∀ i n u v, ⟪P i n u,v⟫_ℝ = ⟪u,P i n v⟫_ℝ)
    (hid : ∀ i n x, P i n (P i n x) = P i n x)
    (hnest : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x)
    (T k : ℕ) (hT : T+1 ≤ 2^k) (m : ℕ) (x : X) :
    (∑ n : Fin T, ‖v19PrefixProduct P (n.val+2) (m+1) x -
      v19PrefixProduct P (n.val+1) (m+1) x‖^2) ≤
      (m+1 : ℝ)^2*(k+1 : ℝ)^(2*m)*‖x‖^2 :=
  v19_normed_product_variation P hz
    (fun i => v19_real_projection_energy (P i) (hsym i) (hid i) (hnest i))
    (fun i n => v19_real_projection_contract (P i n) (hsym i n) (hid i n)) T k hT m x

end OpenAI086
