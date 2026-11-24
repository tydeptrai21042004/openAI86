import Mathlib
import OpenAI086.PaperWeylReturns

/-! Algebraic and subspace steps of the actual Weyl alternative. The
finite short-return directions generate a real isotropic subspace.
Rational height and the lattice-minima/transference estimates remain
separate obligations. -/
namespace OpenAI086
section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Exact chart translation identity, before reducing the integral
lattice term modulo one. No bound on the horizontal oscillation u is
needed for the error term B d (u-n). -/
theorem v39_chart_return_phase (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (u n m d : E) :
    B (u+m+d) ((u+m+d)-(n+m))-B u (u-n) =
      B u d+B m u+B d (u-n)-B m n+B m d+B d d := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

/-- Vanishing of a bilinear form on all generating pairs implies
vanishing on the entire span, including a span of unbounded cardinality. -/
theorem v39_isotropic_span (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (S : Set E)
    (h : ∀ x ∈ S, ∀ y ∈ S, B x y = 0) :
    ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S, B x y = 0 := by
  intro x hx y hy
  have hygen : ∀ z ∈ S, B z y = 0 := by
    intro z hz
    have hsub : Submodule.span ℝ S ≤ LinearMap.ker (B z) :=
      Submodule.span_le.mpr (fun w hw => LinearMap.mem_ker.mpr (h z hz w hw))
    exact LinearMap.mem_ker.mp (hsub hy)
  let L : E →ₗ[ℝ] ℝ :=
    { toFun := fun z => B z y
      map_add' := by intro a b; simp [map_add, LinearMap.add_apply]
      map_smul' := by intro c a; simp [map_smul, LinearMap.smul_apply] }
  have hsub : Submodule.span ℝ S ≤ LinearMap.ker L :=
    Submodule.span_le.mpr (fun z hz => LinearMap.mem_ker.mpr (hygen z hz))
  exact LinearMap.mem_ker.mp (hsub hx)

/-- The effective quadratic identity (page 18) evaluated on two
arbitrary vectors. C is the full chart bilinear form. The fast-fast
symmetry hypothesis is exactly isotropy for C-C^T, not C=0 on U. -/
theorem v39_effective_quadratic (C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (fu su fv sv : E) (hff : C fu fv = C fv fu) :
    C (fu+su) (fv+sv) - (C (fu+su) fv - C fv (fu+su)) =
      (C (fu+su) (fv+sv)+C (fv+sv) (fu+su))/2 +
      (C fu sv-C sv fu)/2 + (C fv su-C su fv)/2 +
      (C su sv-C sv su)/2 := by
  simp only [map_add, LinearMap.add_apply]
  rw [hff]
  ring

end
end OpenAI086
