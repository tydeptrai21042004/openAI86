import OpenAI086.PaperTwoStepCoordinates

/-! Two-step coordinate infrastructure for the degree-two inverse input.
This is not the quantitative inverse theorem: no correlation witness is
constructed. The group law and integral-coordinate subgroup are explicit. -/
namespace OpenAI086

variable {H Z : Type*} [AddCommGroup H] [Module ℝ H]
  [AddCommGroup Z] [Module ℝ Z]

/-- The bilinear cocycle defines a central extension of additive groups. -/
structure V29TwoStep (B : H →ₗ[ℝ] H →ₗ[ℝ] Z) where
  horizontal : H
  central : Z

namespace V29TwoStep
variable (B : H →ₗ[ℝ] H →ₗ[ℝ] Z)

instance : Group (V29TwoStep B) where
  mul a b := ⟨a.horizontal + b.horizontal, a.central + b.central + B a.horizontal b.horizontal⟩
  one := ⟨0, 0⟩
  inv a := ⟨-a.horizontal, -a.central + B a.horizontal a.horizontal⟩
  mul_assoc a b c := by
    cases a; cases b; cases c
    apply V29TwoStep.ext <;> simp [map_add, LinearMap.add_apply] <;> abel
  one_mul a := by cases a; apply V29TwoStep.ext <;> simp
  mul_one a := by cases a; apply V29TwoStep.ext <;> simp
  inv_mul_cancel a := by
    cases a
    apply V29TwoStep.ext <;> simp [map_neg, LinearMap.neg_apply] <;> abel

@[simp] theorem v29_mul_horizontal (a b : V29TwoStep B) :
    (a*b).horizontal = a.horizontal+b.horizontal := rfl
@[simp] theorem v29_mul_central (a b : V29TwoStep B) :
    (a*b).central = a.central+b.central+B a.horizontal b.horizontal := rfl
@[simp] theorem v29_inv_horizontal (a : V29TwoStep B) :
    (a⁻¹).horizontal = -a.horizontal := rfl
@[simp] theorem v29_inv_central (a : V29TwoStep B) :
    (a⁻¹).central = -a.central+B a.horizontal a.horizontal := rfl

/-- Every pure central coordinate commutes with every group element. -/
theorem v29_pure_central_commutes (z : Z) (a : V29TwoStep B) :
    (⟨0,z⟩ : V29TwoStep B)*a = a*⟨0,z⟩ := by
  apply V29TwoStep.ext <;> simp <;> abel

/-- The commutator has zero horizontal coordinate: a two-step group. -/
theorem v29_commutator_horizontal (a b : V29TwoStep B) :
    (a*b*a⁻¹*b⁻¹).horizontal = 0 := by
  simp <;> abel

theorem v29_commutator_centralizes (a b c : V29TwoStep B) :
    (a*b*a⁻¹*b⁻¹)*c = c*(a*b*a⁻¹*b⁻¹) := by
  have h := v29_commutator_horizontal B a b
  apply V29TwoStep.ext <;> simp [h] <;> abel

/-- A lattice candidate from additive subgroups of the horizontal and
central coordinate spaces. Integrality of the cocycle is explicit. This
constructs a subgroup only; discreteness and cocompactness are still open. -/
def v29IntegralSubgroup (LH : AddSubgroup H) (LZ : AddSubgroup Z)
    (hB : ∀ x ∈ LH, ∀ y ∈ LH, B x y ∈ LZ) : Subgroup (V29TwoStep B) where
  carrier := {a | a.horizontal ∈ LH ∧ a.central ∈ LZ}
  one_mem' := ⟨LH.zero_mem, LZ.zero_mem⟩
  mul_mem' := by
    intro a b ha hb
    change a.horizontal ∈ LH ∧ a.central ∈ LZ at ha
    change b.horizontal ∈ LH ∧ b.central ∈ LZ at hb
    exact ⟨LH.add_mem ha.1 hb.1, LZ.add_mem (LZ.add_mem ha.2 hb.2) (hB _ ha.1 _ hb.1)⟩
  inv_mem' := by
    intro a ha
    change a.horizontal ∈ LH ∧ a.central ∈ LZ at ha
    exact ⟨LH.neg_mem ha.1, LZ.add_mem (LZ.neg_mem ha.2) (hB _ ha.1 _ ha.1)⟩

/-- Right cosets, as a quotient of the set of group elements; normality
is not required and the quotient is not asserted to be a group. -/
def v29RightCosetSetoid (Γ : Subgroup (V29TwoStep B)) : Setoid (V29TwoStep B) where
  r a b := a⁻¹*b ∈ Γ
  iseqv := ⟨by intro a; simp,
    by intro a b h; change a⁻¹*b ∈ Γ at h; simpa using Γ.inv_mem h,
    by intro a b c hab hbc
       change a⁻¹*b ∈ Γ at hab
       change b⁻¹*c ∈ Γ at hbc
       have h := Γ.mul_mem hab hbc
       simpa [mul_assoc] using h⟩

end V29TwoStep
end OpenAI086
