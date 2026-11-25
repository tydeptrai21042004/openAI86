import OpenAI086.PaperLemma33Submodules

/-! Paper Lemma 3.3: joint statement for actual nested orthogonal
projections and bounded linear rows. Both conclusions use the precise
binary envelope L_T. No cross-layer commutation is assumed. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable {T : ℕ} {R : Type*} [Fintype R]
variable {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)] [∀ r, NormedSpace 𝕜 (Y r)]

/-- Both inequalities are packaged in one statement. An infinite index
of projection families is a convenient extension of the first m families;
the finite ordered product only uses those first m families. -/
def V43Lemma33Goal (m : ℕ)
    (V : ℕ → Fin (T+1) → Submodule 𝕜 X) [∀ i n, (V i n).HasOrthogonalProjection]
    (N : R → Fin (T+1)) (B : (r : R) → X →L[𝕜] Y r) (x : X) : Prop :=
    Real.sqrt (∑ r, ‖B r (v19FiniteProduct
      (fun i n => (V i n).starProjection.toLinearMap.toAddMonoidHom) (N r) m x)‖^2) ≤
        (v20PaperL T)^m*‖x‖ ∧
    (∑ n : Fin T, ‖v19FiniteProduct
      (fun i k => (V i k).starProjection.toLinearMap.toAddMonoidHom) n.succ m x -
      v19FiniteProduct (fun i k => (V i k).starProjection.toLinearMap.toAddMonoidHom) n.castSucc m x‖^2) ≤
      (m : ℝ)^2*(v20PaperL T)^(2*(m-1))*‖x‖^2

/-- The paper's row estimate and square variation, simultaneously. -/
theorem v43_lemma33 (m : ℕ)
    (V : ℕ → Fin (T+1) → Submodule 𝕜 X) [∀ i n, (V i n).HasOrthogonalProjection]
    (hn : ∀ i a b, a ≤ b → V i a ≤ V i b)
    (N : R → Fin (T+1)) (B : (r : R) → X →L[𝕜] Y r)
    (hrow : ∀ x, (∑ r, ‖B r x‖^2) ≤ ‖x‖^2) (x : X) :
    V43Lemma33Goal m V N B x := by
  constructor
  · exact v22_submodule_prefix (𝕜 := 𝕜) (m := m) V hn N
      (fun r => (B r).toLinearMap.toAddMonoidHom) hrow x
  · exact v22_submodule_variation (𝕜 := 𝕜) m V hn x

end OpenAI086
