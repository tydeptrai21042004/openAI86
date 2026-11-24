import Mathlib
import OpenAI086.PaperLemma33Statement

/-! Lemma 3.3 specialized to actual orthogonal projections onto nested
submodules, rather than maps supplied with algebraic identities. -/
namespace OpenAI086

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

theorem v22_starProjection_moment (V : Submodule 𝕜 X) [V.HasOrthogonalProjection]
    (x w : X) (hw : w ∈ V) : inner 𝕜 (V.starProjection x) w = inner 𝕜 x w := by
  have h := Submodule.starProjection_inner_eq_zero (K := V) x w hw
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem v22_starProjection_symmetric (V : Submodule 𝕜 X) [V.HasOrthogonalProjection]
    (x y : X) : inner 𝕜 (V.starProjection x) y = inner 𝕜 x (V.starProjection y) := by
  have h1 := v22_starProjection_moment V x (V.starProjection y) (V.starProjection_apply_mem y)
  have h2 := v22_starProjection_moment V y (V.starProjection x) (V.starProjection_apply_mem x)
  have h2' := congrArg (starRingEnd 𝕜) h2
  have h3 : inner 𝕜 (V.starProjection x) (V.starProjection y) =
      inner 𝕜 (V.starProjection x) y := by
    simpa only [inner_conj_symm] using h2'
  exact h3.symm.trans h1

theorem v22_starProjection_nested (U V : Submodule 𝕜 X)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V) (x : X) :
    U.starProjection (V.starProjection x) = U.starProjection x := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (U.starProjection_apply_mem x)
  intro w hw
  rw [inner_sub_left, v22_starProjection_moment V x w (hUV hw), v22_starProjection_moment U x w hw, sub_self]

/-- Ordered products of actual nested orthogonal projections, with the
same indexing and logarithmic bound as in the paper. -/
theorem v22_submodule_prefix {T m : ℕ} {R : Type*} [Fintype R]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)]
    (V : ℕ → Fin (T+1) → Submodule 𝕜 X) [∀ i n, (V i n).HasOrthogonalProjection]
    (hn : ∀ i a b, a ≤ b → V i a ≤ V i b)
    (N : R → Fin (T+1)) (B : (r : R) → X →+ Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2) (x : X) :
    Real.sqrt (∑ r, ‖B r (v19FiniteProduct
      (fun i n => (V i n).starProjection.toLinearMap.toAddMonoidHom) (N r) m x)‖^2) ≤
        (v20PaperL T)^m*‖x‖ := by
  apply v21_paper_lemma33_prefix (𝕜 := 𝕜) _ _ _ _ N B hrow x
  · intro i n u v
    exact v22_starProjection_symmetric (V i n) u v
  · intro i n z
    exact (V i n).starProjection_mem_subspace_eq_self ((V i n).starProjection_apply_mem z)
  · intro i a b hab z
    exact v22_starProjection_nested (V i a) (V i b) (hn i a b hab) z

/-- Square variation of actual nested orthogonal projections. -/
theorem v22_submodule_variation {T : ℕ} (m : ℕ)
    (V : ℕ → Fin (T+1) → Submodule 𝕜 X) [∀ i n, (V i n).HasOrthogonalProjection]
    (hn : ∀ i a b, a ≤ b → V i a ≤ V i b) (x : X) :
    (∑ n : Fin T, ‖v19FiniteProduct
      (fun i k => (V i k).starProjection.toLinearMap.toAddMonoidHom) n.succ m x -
      v19FiniteProduct (fun i k => (V i k).starProjection.toLinearMap.toAddMonoidHom) n.castSucc m x‖^2) ≤
      (m : ℝ)^2*(v20PaperL T)^(2*(m-1))*‖x‖^2 := by
  apply v21_paper_lemma33_variation (𝕜 := 𝕜) m _ _ _ _ x
  · intro i n u v
    exact v22_starProjection_symmetric (V i n) u v
  · intro i n z
    exact (V i n).starProjection_mem_subspace_eq_self ((V i n).starProjection_apply_mem z)
  · intro i a b hab z
    exact v22_starProjection_nested (V i a) (V i b) (hn i a b hab) z

end OpenAI086
