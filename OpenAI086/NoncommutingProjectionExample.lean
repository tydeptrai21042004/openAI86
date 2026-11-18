import Mathlib

/-!
# A concrete pair of NONCOMMUTING orthogonal projections on R²

The earlier coordinate-mask model in `CoordinateProjections.lean` is fully
commutative and therefore cannot establish OpenAI #086, Lemma 3.3. Here both
projections are self-adjoint, idempotent, norm contractions, but their ordered
products differ. This example justifies the need for a genuinely
noncommutative estimate rather than treating coordinate masks as general.
-/

namespace OpenAI086

/-- Orthogonal projection onto the first coordinate axis. -/
def axisProjection (z : ℝ × ℝ) : ℝ × ℝ := (z.1, 0)

/-- Orthogonal projection onto the diagonal {(t,t)}. -/
def diagonalProjection (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 + z.2) / 2, (z.1 + z.2) / 2)

/-- Inner product in R². -/
def dot2 (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Squared Euclidean norm in R². -/
def sqNorm2 (u : ℝ × ℝ) : ℝ := u.1 ^ 2 + u.2 ^ 2

theorem axisProjection_idempotent (z : ℝ × ℝ) :
    axisProjection (axisProjection z) = axisProjection z := by
  rfl

theorem diagonalProjection_idempotent (z : ℝ × ℝ) :
    diagonalProjection (diagonalProjection z) = diagonalProjection z := by
  rcases z with ⟨x, y⟩
  apply Prod.ext
  · dsimp [diagonalProjection]
    ring
  · dsimp [diagonalProjection]
    ring

theorem axisProjection_self_adjoint (u v : ℝ × ℝ) :
    dot2 (axisProjection u) v = dot2 u (axisProjection v) := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨a, b⟩
  simp [dot2, axisProjection]

theorem diagonalProjection_self_adjoint (u v : ℝ × ℝ) :
    dot2 (diagonalProjection u) v = dot2 u (diagonalProjection v) := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨a, b⟩
  dsimp [dot2, diagonalProjection]
  ring

theorem axisProjection_contracts_sq (z : ℝ × ℝ) :
    sqNorm2 (axisProjection z) ≤ sqNorm2 z := by
  rcases z with ⟨x, y⟩
  dsimp [sqNorm2, axisProjection]
  nlinarith [sq_nonneg y]

theorem diagonalProjection_contracts_sq (z : ℝ × ℝ) :
    sqNorm2 (diagonalProjection z) ≤ sqNorm2 z := by
  rcases z with ⟨x, y⟩
  dsimp [sqNorm2, diagonalProjection]
  nlinarith [sq_nonneg (x - y)]

/-- Both maps are orthogonal projections, yet they do not commute. -/
theorem orthogonal_projections_need_not_commute :
    axisProjection (diagonalProjection ((1 : ℝ), (0 : ℝ))) ≠
    diagonalProjection (axisProjection ((1 : ℝ), (0 : ℝ))) := by
  intro h
  have hh := congrArg Prod.snd h
  norm_num [axisProjection, diagonalProjection] at hh

end OpenAI086
