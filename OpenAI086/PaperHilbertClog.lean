import Mathlib
import OpenAI086.FiniteHorizonHilbert

/-! Lemma 3.3, exact binary envelope, over real or complex Hilbert spaces.
Realification preserves the norm, addition and self-adjointness. No
finite-dimensional restriction and no cross-layer commutation. -/
namespace OpenAI086

/-- The real-valued logarithmic envelope in Lemma 3.3. -/
noncomputable def v20PaperL (T : ℕ) : ℝ := (Nat.clog 2 (T+1) : ℝ) + 1

theorem v20_clog_envelope (T : ℕ) : T+1 ≤ 2^(Nat.clog 2 (T+1)) :=
  Nat.le_pow_clog (by decide : 1 < (2:ℕ)) (T+1)

theorem v20_clog_minimal (T k : ℕ) (hk : T+1 ≤ 2^k) :
    Nat.clog 2 (T+1) ≤ k := Nat.clog_le_of_le_pow hk

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- Squared first assertion, with exact L_T and heterogeneous row spaces.
Additive maps suffice; bounded linear operators in the paper specialize them. -/
theorem v20_hilbert_prefix_clog {T m : ℕ}
    {R : Type*} [Fintype R] {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, inner 𝕜 (P i n u) v = inner 𝕜 u (P i n v))
    (hi : ∀ i n x, P i n (P i n x) = P i n x)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x)
    (N : R → Fin (T+1)) (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2) (x : X) :
    (∑ r, ‖B r (v19FiniteProduct P (N r) m x)‖^2) ≤
      (v20PaperL T)^(2*m)*‖x‖^2 := by
  letI : InnerProductSpace ℝ X := InnerProductSpace.rclikeToReal 𝕜 X
  have hr : ∀ i n u v, inner ℝ (P i n u) v = inner ℝ u (P i n v) := by
    intro i n u v
    change RCLike.re (inner 𝕜 (P i n u) v) = RCLike.re (inner 𝕜 u (P i n v))
    rw [hs]
  simpa only [v20PaperL] using
    v19_finite_horizon_prefix (m := m) (v20_clog_envelope T) P hr hi hn N B hrow x

/-- Exact square variation, including the empty product. -/
theorem v20_hilbert_variation_clog {T : ℕ} (m : ℕ)
    (P : ℕ → Fin (T+1) → X →+ X)
    (hs : ∀ i n u v, inner 𝕜 (P i n u) v = inner 𝕜 u (P i n v))
    (hi : ∀ i n x, P i n (P i n x) = P i n x)
    (hn : ∀ i a b, a ≤ b → ∀ x, P i a (P i b x) = P i a x) (x : X) :
    (∑ n : Fin T, ‖v19FiniteProduct P n.succ m x -
      v19FiniteProduct P n.castSucc m x‖^2) ≤
      (m : ℝ)^2*(v20PaperL T)^(2*(m-1))*‖x‖^2 := by
  letI : InnerProductSpace ℝ X := InnerProductSpace.rclikeToReal 𝕜 X
  have hr : ∀ i n u v, inner ℝ (P i n u) v = inner ℝ u (P i n v) := by
    intro i n u v
    change RCLike.re (inner 𝕜 (P i n u) v) = RCLike.re (inner 𝕜 u (P i n v))
    rw [hs]
  cases m with
  | zero => simp [v19FiniteProduct]
  | succ m =>
    simpa [v20PaperL, Nat.cast_succ] using
      v19_finite_horizon_variation (m := m) (v20_clog_envelope T) P hr hi hn x

end OpenAI086
