import Mathlib

/-! Theorem 4.7: discrete interval U³ normalization infrastructure only.
The paper invokes Leng–Sah–Sawhney, not a finite correlation surrogate.
No inverse theorem is asserted here. The filtered nilmanifold, polynomial
orbit, Lipschitz witness, and quantitative complexity remain to be built. -/
namespace OpenAI086

/-- Zero extension of [0,L) into the cyclic group of size 16L. -/
def v27IntervalExtend (L : ℕ) (f : Fin L → ℂ) (x : ZMod (16*L)) : ℂ :=
  if hx : x.val < L then f ⟨x.val,hx⟩ else 0

/-- Raw cube average with conjugation at odd vertices. The normalization
is Haar probability on the four cyclic variables. -/
noncomputable def v27RawCube (L : ℕ) [NeZero (16*L)]
    (f : ZMod (16*L) → ℂ) : ℂ :=
  (∑ x : ZMod (16*L), ∑ h : Fin 3 → ZMod (16*L),
    ∏ ω : Fin 3 → Fin 2,
      let z := f (x + ∑ i : Fin 3, ((ω i).val : ZMod (16*L))*h i)
      if (∑ i : Fin 3, (ω i).val) % 2 = 0 then z else star z) /
    ((16*L : ℕ) : ℂ)^4

/-- Eighth power of the interval U³ quantity as a normalized raw-cube
ratio. Nonnegativity and positivity of the indicator denominator are
separate obligations, not imposed by truncation. -/
noncomputable def v27IntervalCubeRatio (L : ℕ) [NeZero (16*L)]
    (f : Fin L → ℂ) : ℝ :=
  (v27RawCube L (v27IntervalExtend L f)).re /
    (v27RawCube L (v27IntervalExtend L (fun _ => 1))).re

end OpenAI086
