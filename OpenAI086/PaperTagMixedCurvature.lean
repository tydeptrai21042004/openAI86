import Mathlib

/-! Lemma 6.1, p.40: the opposite mixed curvature coefficients and the
persistence of a bounded-scale Weyl witness under halving. -/
namespace OpenAI086

def v27SlotWeight (i : Fin 4) : ℚ := ![-1,3,-3,1] i

theorem v27_mixed_curvature (i j a b : Fin 4)
    (hij : i ≠ j) (hia : i ≠ a) (hib : i ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b) :
    let xi := fun l : Fin 4 => ((b.val : ℚ)-(l.val : ℚ))/((b.val : ℚ)-(a.val : ℚ))
    let ze := fun l : Fin 4 => ((l.val : ℚ)-(a.val : ℚ))/((b.val : ℚ)-(a.val : ℚ))
    v27SlotWeight i*xi i*ze i = -(v27SlotWeight j*xi j*ze j) ∧
      v27SlotWeight i*xi i*ze i ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp_all [v27SlotWeight] <;> norm_num

/-- The same rational fast-space witness works at the next dyadic scale:
slow horizontal data scale by 1/2 and effective curvature by 1/4. -/
theorem v27_halving_witness (V Q H : ℝ) (hH : 0 ≤ H)
    (hV : |V| ≤ H) (hQ : |Q| ≤ H) : |V/2| ≤ H ∧ |Q/4| ≤ H := by
  rw [abs_div, abs_div]
  norm_num
  constructor <;> linarith

end OpenAI086
