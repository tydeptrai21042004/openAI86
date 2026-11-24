import Mathlib
import OpenAI086.PaperCramerNumerators

/-! Lemma 8.2: choose basis vectors from the defining rational family,
and a nonsingular coordinate minor from independent columns. -/
namespace OpenAI086

/-- The basis is selected from the original family, so any height bound
on that family is retained unchanged. -/
theorem v22_rational_basis_selection {I J : Type*} (v : I → J → ℚ) :
    ∃ (K : Type _) (a : K → I), Function.Injective a ∧
      Submodule.span ℚ (Set.range (v ∘ a)) = Submodule.span ℚ (Set.range v) ∧
      LinearIndependent ℚ (v ∘ a) :=
  exists_linearIndependent' ℚ v

/-- Surjectivity of a square rational matrix supplies a right inverse,
which proves nonvanishing determinant directly. -/
theorem v22_det_ne_zero_of_surjective {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (h : Function.Surjective A.mulVec) : A.det ≠ 0 := by
  classical
  choose w hw using fun j : I => h (fun i => if i = j then (1:ℚ) else 0)
  let B : Matrix I I ℚ := fun i j => w j i
  have hAB : A*B = 1 := by
    ext i j
    have hh := congrFun (hw j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B, Matrix.one_apply] using hh
  have hd := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

/-- Choose actual row coordinates of a full-column-rank rational matrix.
No invertible minor or coordinate selection is assumed. -/
theorem v22_invertible_coordinate_minor {J I : Type*} [Fintype J] [Fintype I]
    [DecidableEq I] (A : Matrix J I ℚ) (hcol : LinearIndependent ℚ A.col) :
    ∃ a : I → J, Function.Injective a ∧ (A.submatrix a id).det ≠ 0 := by
  classical
  have ht : LinearIndependent ℚ A.transpose.row := hcol
  have hrank : A.rank = Fintype.card I := by
    simpa only [Matrix.rank_transpose] using ht.rank_matrix
  obtain ⟨K, f, hf, hspan, hlin⟩ := exists_linearIndependent' ℚ A.row
  letI : Finite K := Finite.of_injective f hf
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card I := by
    calc
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range (A.row ∘ f))) :=
        (finrank_span_eq_card hlin).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range A.row)) := by rw [hspan]
      _ = A.rank := (Matrix.rank_eq_finrank_span_row A).symm
      _ = _ := hrank
  let e : I ≃ K := Fintype.equivOfCardEq hcard.symm
  let a : I → J := f ∘ e
  have hlin' : LinearIndependent ℚ (A.submatrix a id).row := by
    change LinearIndependent ℚ ((A.row ∘ f) ∘ e)
    exact hlin.comp e e.injective
  exact ⟨a, hf.comp e.injective,
    v22_det_ne_zero_of_surjective (A.submatrix a id) hlin'.mulVec_surjective⟩

end OpenAI086
