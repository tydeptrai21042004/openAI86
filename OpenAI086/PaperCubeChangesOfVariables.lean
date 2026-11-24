import Mathlib

/-! The two four-coordinate Haar changes of variables in Lemma 4.8
(p. 23). These explicit inverses work in every additive commutative group,
including the torus. Measure preservation and cube Cauchy–Schwarz remain open. -/
namespace OpenAI086

/-- The vertices 000,100,010,001 of the three-dimensional cube. -/
def v18CubeLow {G : Type*} [AddCommGroup G] (z : G × G × G × G) :
    G × G × G × G :=
  (z.1, z.1+z.2.1, z.1+z.2.2.1, z.1+z.2.2.2)

def v18CubeLowInv {G : Type*} [AddCommGroup G] (w : G × G × G × G) :
    G × G × G × G :=
  (w.1, w.2.1-w.1, w.2.2.1-w.1, w.2.2.2-w.1)

/-- The complementary vertices 111,011,101,110. -/
def v18CubeHigh {G : Type*} [AddCommGroup G] (z : G × G × G × G) :
    G × G × G × G :=
  (z.1+z.2.1+z.2.2.1+z.2.2.2, z.1+z.2.2.1+z.2.2.2,
    z.1+z.2.1+z.2.2.2, z.1+z.2.1+z.2.2.1)

def v18CubeHighInv {G : Type*} [AddCommGroup G] (w : G × G × G × G) :
    G × G × G × G :=
  (w.2.1+w.2.2.1+w.2.2.2-w.1-w.1,
    w.1-w.2.1, w.1-w.2.2.1, w.1-w.2.2.2)

theorem v18_cube_low_left_inverse {G : Type*} [AddCommGroup G]
    (z : G × G × G × G) : v18CubeLowInv (v18CubeLow z) = z := by
  rcases z with ⟨x,a,b,c⟩
  simp only [v18CubeLow, v18CubeLowInv, Prod.mk.injEq]
  (try constructor) <;> (try constructor) <;> (try constructor) <;> abel

theorem v18_cube_low_right_inverse {G : Type*} [AddCommGroup G]
    (w : G × G × G × G) : v18CubeLow (v18CubeLowInv w) = w := by
  rcases w with ⟨x,a,b,c⟩
  simp only [v18CubeLow, v18CubeLowInv, Prod.mk.injEq]
  (try constructor) <;> (try constructor) <;> (try constructor) <;> abel

theorem v18_cube_high_left_inverse {G : Type*} [AddCommGroup G]
    (z : G × G × G × G) : v18CubeHighInv (v18CubeHigh z) = z := by
  rcases z with ⟨x,a,b,c⟩
  simp only [v18CubeHigh, v18CubeHighInv, Prod.mk.injEq]
  (try constructor) <;> (try constructor) <;> (try constructor) <;> abel

theorem v18_cube_high_right_inverse {G : Type*} [AddCommGroup G]
    (w : G × G × G × G) : v18CubeHigh (v18CubeHighInv w) = w := by
  rcases w with ⟨x,a,b,c⟩
  simp only [v18CubeHigh, v18CubeHighInv, Prod.mk.injEq]
  (try constructor) <;> (try constructor) <;> (try constructor) <;> abel

end OpenAI086
