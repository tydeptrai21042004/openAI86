import Mathlib

/-! Proposition 9.3: exact amplitude exponents and their strictly negative
partial sums, with an explicit admissible interpolation parameter. -/
namespace OpenAI086

theorem v23_amplitude_exponents (p0 θ : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1/4) :
    let p := 1-θ+θ*p0
    let e1 := p-2*(1-θ)
    let e2 := p-2*(1-θ)
    let e3 := p
    let e4 := p-4*θ*p0
    e1+e2+e3+e4=0 ∧ e1<0 ∧ e1+e2<0 ∧ e1+e2+e3<0 ∧ 2/3<p := by
  dsimp
  have hh : θ*p0 < θ := by nlinarith [mul_pos hθ (sub_pos.mpr hp1)]
  refine ⟨by ring, by linarith, by linarith, by linarith, ?_⟩
  nlinarith [mul_pos hθ hp0]

end OpenAI086
