import OpenAI086.PaperHilbertClog

/-! Lemma 3.3 paper-facing entrypoint. The first assertion is written in
its original square-root form. The second retains the square variation.
The underlying self-adjoint idempotent additive maps include orthogonal
linear projections; no commutation between layers is required. -/
namespace OpenAI086

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

theorem v21_paper_L_nonneg (T : ℕ) : 0 ≤ v20PaperL T := by
  unfold v20PaperL
  positivity

theorem v21_paper_lemma33_prefix {T m : ℕ}
    {R : Type*} [Fintype R] {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, inner 𝕜 (P i n u) v = inner 𝕜 u (P i n v))
    (hi : ∀ i n x, P i n (P i n x) = P i n x)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x)
    (N : R → Fin (T+1)) (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2) (x : X) :
    Real.sqrt (∑ r, ‖B r (v19FiniteProduct P (N r) m x)‖^2) ≤
      (v20PaperL T)^m*‖x‖ := by
  have h := v20_hilbert_prefix_clog (𝕜 := 𝕜) (m := m) P hs hi hn N B hrow x
  have hS : 0 ≤ (∑ r, ‖B r (v19FiniteProduct P (N r) m x)‖^2) :=
    Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hL : 0 ≤ (v20PaperL T)^m*‖x‖ :=
    mul_nonneg (pow_nonneg (v21_paper_L_nonneg T) m) (norm_nonneg _)
  have hsq : (Real.sqrt (∑ r, ‖B r (v19FiniteProduct P (N r) m x)‖^2))^2 ≤
      ((v20PaperL T)^m*‖x‖)^2 := by
    rw [Real.sq_sqrt hS, mul_pow, ← pow_mul]
    simpa [Nat.mul_comm] using h
  nlinarith [Real.sqrt_nonneg (∑ r, ‖B r (v19FiniteProduct P (N r) m x)‖^2)]

theorem v21_paper_lemma33_variation {T : ℕ} (m : ℕ)
    (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, inner 𝕜 (P i n u) v = inner 𝕜 u (P i n v))
    (hi : ∀ i n x, P i n (P i n x) = P i n x)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x) (x : X) :
    (∑ n : Fin T, ‖v19FiniteProduct P n.succ m x -
      v19FiniteProduct P n.castSucc m x‖^2) ≤
      (m : ℝ)^2*(v20PaperL T)^(2*(m-1))*‖x‖^2 :=
  v20_hilbert_variation_clog (𝕜 := 𝕜) m P hs hi hn x

end OpenAI086
