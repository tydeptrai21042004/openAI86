import Mathlib

/-! Section 2, page 6: bounded extension by density.  We use three successive
linear extensions, with spaces of continuous linear maps as Banach targets.
The input is an actual curried trilinear map on the dense subspace and its
product norm estimate, not the desired extension.  The singular-integral
bound and identification of that map with the PV remain separate obligations.
Source candidate: must be checked against the pinned Mathlib toolchain. -/

noncomputable section
namespace OpenAI086

section DenseExtension
variable {D A X Y : Type*}
  [AddCommGroup D] [Module ℂ D] [AddCommGroup A] [Module ℂ A]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Extend a linearly parametrized family while preserving its parameter
linearity. The norm estimate is needed only for the original dense data. -/
def v24ExtendFamily (e : D →ₗ[ℂ] X) (hd : DenseRange e)
    (F : A →ₗ[ℂ] D →ₗ[ℂ] Y)
    (hb : ∀ a, ∃ C : ℝ, ∀ d, ‖F a d‖ ≤ C * ‖e d‖) :
    A →ₗ[ℂ] (X →L[ℂ] Y) where
  toFun a := (F a).extendOfNorm e
  map_add' a b := by
    obtain ⟨C, hC⟩ := hb (a+b)
    apply LinearMap.extendOfNorm_unique hd C hC
    apply LinearMap.ext
    intro d
    change ((F a).extendOfNorm e) (e d) + ((F b).extendOfNorm e) (e d) = F (a+b) d
    rw [LinearMap.extendOfNorm_eq hd (hb a), LinearMap.extendOfNorm_eq hd (hb b)]
    simp
  map_smul' c a := by
    obtain ⟨C, hC⟩ := hb (c • a)
    apply LinearMap.extendOfNorm_unique hd C hC
    apply LinearMap.ext
    intro d
    change c • (((F a).extendOfNorm e) (e d)) = F (c • a) d
    rw [LinearMap.extendOfNorm_eq hd (hb a)]
    simp

theorem v24_extend_family_agrees (e : D →ₗ[ℂ] X) (hd : DenseRange e)
    (F : A →ₗ[ℂ] D →ₗ[ℂ] Y)
    (hb : ∀ a, ∃ C : ℝ, ∀ d, ‖F a d‖ ≤ C * ‖e d‖) (a : A) (d : D) :
    v24ExtendFamily e hd F hb a (e d) = F a d := by
  exact LinearMap.extendOfNorm_eq hd (hb a) d

theorem v24_extend_family_norm (e : D →ₗ[ℂ] X) (hd : DenseRange e)
    (F : A →ₗ[ℂ] D →ₗ[ℂ] Y)
    (hb : ∀ a, ∃ C : ℝ, ∀ d, ‖F a d‖ ≤ C * ‖e d‖)
    (a : A) (C : ℝ) (hC : 0 ≤ C) (h : ∀ d, ‖F a d‖ ≤ C * ‖e d‖) :
    ‖v24ExtendFamily e hd F hb a‖ ≤ C := by
  exact LinearMap.opNorm_extendOfNorm_le hd hC h

/-- Continuous maps agreeing on the dense image are equal. -/
theorem v24_dense_clm_ext (e : D →ₗ[ℂ] X) (hd : DenseRange e)
    (F G : X →L[ℂ] Y) (h : ∀ d, F (e d) = G (e d)) : F = G := by
  apply ContinuousLinearMap.ext
  intro x
  exact hd.induction_on x (isClosed_eq F.continuous G.continuous) h

end DenseExtension

section ThreeSlots
variable {D X Y : Type*} [AddCommGroup D] [Module ℂ D]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

variable (e : D →ₗ[ℂ] X) (hd : DenseRange e)
  (T : D →ₗ[ℂ] D →ₗ[ℂ] D →ₗ[ℂ] Y) (C : ℝ)
  (hC : 0 ≤ C) (hT : ∀ a b c, ‖T a b c‖ ≤ C * ‖e a‖ * ‖e b‖ * ‖e c‖)

/-- Extend the third slot, keeping the first two algebraically linear. -/
def v24Third : D →ₗ[ℂ] D →ₗ[ℂ] (X →L[ℂ] Y) where
  toFun a := v24ExtendFamily e hd (T a) (fun b => ⟨C * ‖e a‖ * ‖e b‖, hT a b⟩)
  map_add' a b := by
    apply LinearMap.ext
    intro d
    apply v24_dense_clm_ext e hd
    intro c
    change v24ExtendFamily e hd (T (a+b)) _ d (e c) =
      v24ExtendFamily e hd (T a) _ d (e c) + v24ExtendFamily e hd (T b) _ d (e c)
    simp only [v24_extend_family_agrees, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro d
    apply v24_dense_clm_ext e hd
    intro c
    change v24ExtendFamily e hd (T (r • a)) _ d (e c) =
      r • v24ExtendFamily e hd (T a) _ d (e c)
    simp only [v24_extend_family_agrees, map_smul, LinearMap.smul_apply]

theorem v24_third_agrees (a b c : D) :
    v24Third e hd T C hT a b (e c) = T a b c := by
  exact v24_extend_family_agrees e hd (T a) _ b c

include hC in
theorem v24_third_norm (a b : D) :
    ‖v24Third e hd T C hT a b‖ ≤ C * ‖e a‖ * ‖e b‖ := by
  exact v24_extend_family_norm e hd (T a) _ b _ (by positivity) (hT a b)

/-- Extend the second slot into the complete space of bounded maps. -/
def v24Second : D →ₗ[ℂ] (X →L[ℂ] (X →L[ℂ] Y)) :=
  v24ExtendFamily e hd (v24Third e hd T C hT)
    (fun a => ⟨C * ‖e a‖, v24_third_norm e hd T C hC hT a⟩)

theorem v24_second_agrees (a b : D) :
    v24Second e hd T C hC hT a (e b) = v24Third e hd T C hT a b := by
  exact v24_extend_family_agrees e hd _ _ a b

theorem v24_second_norm (a : D) :
    ‖v24Second e hd T C hC hT a‖ ≤ C * ‖e a‖ := by
  exact v24_extend_family_norm e hd _ _ a _ (by positivity)
    (v24_third_norm e hd T C hC hT a)

/-- The actual bounded extension as a curried continuous trilinear operator. -/
def v24TrilinearExtension : X →L[ℂ] (X →L[ℂ] (X →L[ℂ] Y)) :=
  (v24Second e hd T C hC hT).extendOfNorm e

theorem v24_extension_agrees (a b c : D) :
    v24TrilinearExtension e hd T C hC hT (e a) (e b) (e c) = T a b c := by
  unfold v24TrilinearExtension
  rw [LinearMap.extendOfNorm_eq hd ⟨C, v24_second_norm e hd T C hC hT⟩ a,
    v24_second_agrees, v24_third_agrees]

theorem v24_extension_opNorm : ‖v24TrilinearExtension e hd T C hC hT‖ ≤ C := by
  exact LinearMap.opNorm_extendOfNorm_le hd hC (v24_second_norm e hd T C hC hT)

theorem v24_extension_product_bound (a b c : X) :
    ‖v24TrilinearExtension e hd T C hC hT a b c‖ ≤ C * ‖a‖ * ‖b‖ * ‖c‖ := by
  let S := v24TrilinearExtension e hd T C hC hT
  have h₁ : ‖S a‖ ≤ C * ‖a‖ :=
    (S.le_opNorm a).trans (mul_le_mul_of_nonneg_right (v24_extension_opNorm e hd T C hC hT) (norm_nonneg a))
  have h₂ : ‖S a b‖ ≤ C * ‖a‖ * ‖b‖ :=
    ((S a).le_opNorm b).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg b))
  exact ((S a b).le_opNorm c).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg c))

theorem v24_extension_unique
    (S : X →L[ℂ] (X →L[ℂ] (X →L[ℂ] Y)))
    (hS : ∀ a b c : D, S (e a) (e b) (e c) = T a b c) :
    S = v24TrilinearExtension e hd T C hC hT := by
  apply v24_dense_clm_ext e hd
  intro a
  apply v24_dense_clm_ext e hd
  intro b
  apply v24_dense_clm_ext e hd
  intro c
  exact (hS a b c).trans (v24_extension_agrees e hd T C hC hT a b c).symm

end ThreeSlots

open MeasureTheory
abbrev V24L3 := Lp ℂ 3 (volume : Measure ℝ)
abbrev V24L1 := Lp ℂ 1 (volume : Measure ℝ)
abbrev V24Schwartz := SchwartzMap ℝ ℂ

noncomputable def v24SchwartzEmbedding : V24Schwartz →ₗ[ℂ] V24L3 :=
  (SchwartzMap.toLpCLM ℂ ℂ 3 (volume : Measure ℝ)).toLinearMap

theorem v24_schwartz_dense : DenseRange v24SchwartzEmbedding := by
  change DenseRange (fun f : V24Schwartz => f.toLp 3 (volume : Measure ℝ))
  simpa only [SchwartzMap.toLpCLM_apply] using
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 3)
      (μ := (volume : Measure ℝ)) (by norm_num))

/-- The consequence on p.6: once the actual Schwartz operator and its bound
are supplied, a unique bounded trilinear L3-to-L1 operator exists. -/
theorem v24_L3_extension
    (T : V24Schwartz →ₗ[ℂ] V24Schwartz →ₗ[ℂ] V24Schwartz →ₗ[ℂ] V24L1)
    (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ a b c, ‖T a b c‖ ≤ C * ‖v24SchwartzEmbedding a‖ *
        ‖v24SchwartzEmbedding b‖ * ‖v24SchwartzEmbedding c‖) :
    ∃! S : V24L3 →L[ℂ] (V24L3 →L[ℂ] (V24L3 →L[ℂ] V24L1)),
      (∀ a b c, S (v24SchwartzEmbedding a) (v24SchwartzEmbedding b)
        (v24SchwartzEmbedding c) = T a b c) ∧ ‖S‖ ≤ C := by
  refine ⟨v24TrilinearExtension v24SchwartzEmbedding v24_schwartz_dense T C hC hT,
    ⟨v24_extension_agrees _ _ _ _ _ _, v24_extension_opNorm _ _ _ _ _ _⟩, ?_⟩
  intro S hS
  exact v24_extension_unique _ _ _ _ _ _ S hS.1

end OpenAI086
