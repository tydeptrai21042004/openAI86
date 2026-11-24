import OpenAI086.PaperDiscreteInverseDomain

/-! Exact cube energy on any finite additive commutative group.
The connection with the indexed eight-vertex definition is explicit.
This is normalization infrastructure, not the quantitative inverse theorem. -/
namespace OpenAI086
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def v28Face (f : G → ℂ) (a b x : G) : ℂ :=
  f x * star (f (x+a)) * star (f (x+b)) * f (x+a+b)

theorem v28_translate_sum (g : G → ℂ) (x : G) :
    (∑ h : G, g (x+h)) = ∑ h : G, g h := by
  let e : G ≃ G := {
    toFun := fun h => x+h
    invFun := fun h => h-x
    left_inv := by intro h; dsimp; abel
    right_inv := by intro h; dsimp; abel }
  exact Equiv.sum_comp e g

theorem v28_star_self (z : ℂ) : z * star z = (‖z‖^2 : ℝ) := by
  change z * (starRingEnd ℂ) z = ((‖z‖^2 : ℝ) : ℂ)
  rw [Complex.sq_norm]
  exact Complex.mul_conj z

/-- Summing the last translation produces an actual square of a sum. -/
theorem v28_correlation_energy (g : G → ℂ) :
    (∑ x : G, ∑ h : G, g x * star (g (x+h))) =
      ((‖∑ x : G, g x‖^2 : ℝ) : ℂ) := by
  calc
    _ = ∑ x : G, g x * (∑ h : G, star (g (x+h))) := by
      apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
    _ = ∑ x : G, g x * (∑ h : G, star (g h)) := by
      apply Finset.sum_congr rfl; intro x _
      rw [v28_translate_sum (fun h => star (g h)) x]
    _ = (∑ x : G, g x) * (∑ h : G, star (g h)) := by rw [Finset.sum_mul]
    _ = (∑ x : G, g x) * star (∑ x : G, g x) := by
      rw [show (∑ h : G, star (g h)) = star (∑ h : G, g h) from
        (map_sum (starRingEnd ℂ) g Finset.univ).symm]
    _ = _ := v28_star_self _

/-- Exact eight-vertex factorization in the same indexing as V27. -/
theorem v28_indexed_cube_factor (f : G → ℂ) (x : G) (h : Fin 3 → G) :
    (∏ ω : Fin 3 → Fin 2,
      let z := f (x + ∑ i : Fin 3, (ω i).val • h i)
      if (∑ i : Fin 3, (ω i).val) % 2 = 0 then z else star z) =
      v28Face f (h 0) (h 1) x * star (v28Face f (h 0) (h 1) (x+h 2)) := by
  have hu : (Finset.univ : Finset (Fin 3 → Fin 2)) =
      {![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
       ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]} := by decide
  rw [hu]
  simp (disch := decide) [Finset.prod_insert, Fin.sum_univ_three, v28Face, star_mul,
    add_assoc, add_comm, add_left_comm] <;> ring

/-- Reindex the three independent group variables, without an assumed
bijection or an enumeration of the group itself. -/
theorem v28_sum_fin_three (F : (Fin 3 → G) → ℂ) :
    (∑ h, F h) = ∑ a : G, ∑ b : G, ∑ c : G, F ![a,b,c] := by
  classical
  let e : G × G × G ≃ (Fin 3 → G) := {
    toFun := fun p => ![p.1,p.2.1,p.2.2]
    invFun := fun h => (h 0,h 1,h 2)
    left_inv := by intro p; rcases p with ⟨a,b,c⟩; rfl
    right_inv := by intro h; funext i; fin_cases i <;> rfl }
  rw [← Equiv.sum_comp e F]
  simp [Fintype.sum_prod_type, e]

/-- The finite cyclic cube in V27 is a nonnegative real energy, not a
real-part truncation of an arbitrary complex expression. -/
theorem v28_raw_cube_energy (L : ℕ) [NeZero (16*L)]
    (f : ZMod (16*L) → ℂ) :
    v27RawCube L f = (((∑ a : ZMod (16*L), ∑ b : ZMod (16*L),
      ‖∑ x : ZMod (16*L), v28Face f a b x‖^2) /
        ((16*L : ℕ) : ℝ)^4 : ℝ) : ℂ) := by
  classical
  unfold v27RawCube
  push_cast
  congr 1
  calc
    _ = ∑ x : ZMod (16*L), ∑ h : Fin 3 → ZMod (16*L),
        v28Face f (h 0) (h 1) x * star (v28Face f (h 0) (h 1) (x+h 2)) := by
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro h _
      simpa only [nsmul_eq_mul] using v28_indexed_cube_factor f x h
    _ = ∑ x : ZMod (16*L), ∑ a : ZMod (16*L), ∑ b : ZMod (16*L),
        ∑ c : ZMod (16*L), v28Face f a b x * star (v28Face f a b (x+c)) := by
      apply Finset.sum_congr rfl; intro x _
      simpa using v28_sum_fin_three (fun h =>
        v28Face f (h 0) (h 1) x * star (v28Face f (h 0) (h 1) (x+h 2)))
    _ = ∑ a : ZMod (16*L), ∑ b : ZMod (16*L),
        ∑ x : ZMod (16*L), ∑ c : ZMod (16*L),
          v28Face f a b x * star (v28Face f a b (x+c)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
    _ = _ := by
      push_cast
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      exact v28_correlation_energy (v28Face f a b)

theorem v28_raw_cube_nonnegative (L : ℕ) [NeZero (16*L)] (f : ZMod (16*L) → ℂ) :
    0 ≤ (v27RawCube L f).re := by
  rw [v28_raw_cube_energy, Complex.ofReal_re]
  positivity

theorem v28_raw_cube_real (L : ℕ) [NeZero (16*L)] (f : ZMod (16*L) → ℂ) :
    (v27RawCube L f).im = 0 := by
  rw [v28_raw_cube_energy, Complex.ofReal_im]

end OpenAI086
