import Mathlib
import OpenAI086.PaperSeparatedRows

/-! Lemma 8.7 and Proposition 8.9: the actual affine derivative test in
(22), PRE connectivity, and projection leakage from small cross pairings.
The integration-by-parts estimate and Fourier series construction are
separate analytic obligations. -/
namespace OpenAI086

/-- Affine derivative of a difference of two quadratic modes, with a
fixed rational-frequency witness shift. -/
def v22ModeDerivative (λ γ shift x : ℝ) : ℝ := 2*λ*x+γ+shift

theorem v22_affine_derivative_variation (λ γ shift x y R : ℝ)
    (hxy : |x-y| ≤ R) :
    |v22ModeDerivative λ γ shift x-v22ModeDerivative λ γ shift y| ≤ 2*|λ|*R := by
  have he : v22ModeDerivative λ γ shift x-v22ModeDerivative λ γ shift y = 2*λ*(x-y) := by
    unfold v22ModeDerivative; ring
  rw [he, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hxy (by positivity)

/-- Nonadjacency supplies one large derivative value. The slope
oscillation bound then makes it large everywhere on the cell. -/
theorem v22_derivative_uniform_lower (λ γ shift x y R A : ℝ)
    (hxy : |x-y| ≤ R) (hlarge : A < |v22ModeDerivative λ γ shift y|)
    (hsmall : 2*|λ|*R ≤ A/2) : A/2 < |v22ModeDerivative λ γ shift x| := by
  have hv := (v22_affine_derivative_variation λ γ shift x y R hxy).trans hsmall
  have he : v22ModeDerivative λ γ shift y = v22ModeDerivative λ γ shift x -
    (v22ModeDerivative λ γ shift x-v22ModeDerivative λ γ shift y) := by ring
  have ht : |v22ModeDerivative λ γ shift y| ≤ |v22ModeDerivative λ γ shift x|+
    |v22ModeDerivative λ γ shift x-v22ModeDerivative λ γ shift y| := by
    conv_lhs => rw [he]
    exact abs_sub _ _
  linarith

/-- Equation (22), with the shift set representing n·ϑ/L_h and the
cell an arbitrary subset of the real line. -/
def v22PreEdge {M : Type*} (J : Set ℝ) (shifts : Set ℝ) (A : ℝ)
    (λ γ : M → ℝ) (m m' : M) : Prop :=
  ∃ s ∈ shifts, ∀ x ∈ J, |v22ModeDerivative (λ m-λ m') (γ m-γ m') s x| ≤ A

/-- Old witnesses persist when the shift set grows, the cell shrinks,
and the graph threshold increases. -/
theorem v22_pre_edge_persistent {M : Type*} (J K shifts shifts' : Set ℝ)
    (A B : ℝ) (λ γ : M → ℝ) (m m' : M)
    (hJ : K ⊆ J) (hs : shifts ⊆ shifts') (hA : A ≤ B)
    (h : v22PreEdge J shifts A λ γ m m') : v22PreEdge K shifts' B λ γ m m' := by
  rcases h with ⟨s, hs', hbound⟩
  exact ⟨s, hs hs', fun x hx => (hbound x (hJ hx)).trans hA⟩

/-- Different connected components have no edge. This is stated on the
actual relation rather than an assumed component-number array. -/
theorem v22_pre_no_edge_between_components {M : Type*} (edge : M → M → Prop)
    (m m' : M) (h : ¬ Relation.ReflTransGen edge m m') : ¬ edge m m' := by
  intro he
  exact h (Relation.ReflTransGen.single he)

/-- Duality proof for a projection leakage bound. The hypothesis is a
bound on pairings with the range, not a bound on the projected norm. -/
theorem v22_projection_leakage {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (P : X →+ X) (z : X) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v))
    (hi : ∀ x, P (P x) = P x)
    (hpair : ∀ w, P w = w → |inner ℝ z w| ≤ ε*‖w‖) : ‖P z‖ ≤ ε := by
  have hp := hpair (P z) (hi z)
  have he : inner ℝ z (P z) = ‖P z‖^2 := by
    calc
      _ = inner ℝ z (P (P z)) := by rw [hi]
      _ = inner ℝ (P z) (P z) := (hs z (P z)).symm
      _ = _ := real_inner_self_eq_norm_sq _
  rw [he, abs_of_nonneg (sq_nonneg _)] at hp
  by_contra! hn
  have hpos : 0 < ‖P z‖ := lt_of_le_of_lt hε hn
  nlinarith [mul_pos hpos (sub_pos.mpr hn)]

/-- Sum Fourier head contributions plus the tail, with the paper's
absolute-coefficient-sum bound. This does not assert the derivative
integral estimate used to establish hmode. -/
theorem v22_fourier_pair_budget {I : Type*} [Fintype I]
    (c mode : I → ℂ) (tail : ℂ) (B A ε : ℝ) (hA : 0 ≤ A)
    (hcoeff : (∑ i, ‖c i‖) ≤ B) (hmode : ∀ i, ‖mode i‖ ≤ A)
    (htail : ‖tail‖ ≤ ε) : ‖(∑ i, c i*mode i)+tail‖ ≤ B*A+ε := by
  calc
    _ ≤ ‖∑ i, c i*mode i‖+‖tail‖ := norm_add_le _ _
    _ ≤ (∑ i, ‖c i*mode i‖)+‖tail‖ := add_le_add_right (norm_sum_le _ _) _
    _ ≤ (∑ i, ‖c i‖*A)+ε := by
      apply add_le_add _ htail
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmode i) (norm_nonneg _)
    _ = (∑ i, ‖c i‖)*A+ε := by rw [Finset.sum_mul]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hA) _

end OpenAI086
