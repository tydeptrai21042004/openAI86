import Mathlib

/-!
# Lemma 3.3: why the *row* estimate is not the m = 1 energy estimate

The square variation of one nested orthogonal-projection family has
a unit bound, but the first assertion of Lemma 3.3 asks about different
row operators Bν applied at *different* prefix indices.  Even with two
prefixes and a Parseval pair of rows, the corresponding best bound is
strictly greater than one.  These explicit rational data prevent an
incorrect attempt to "prove" the first assertion using only telescoping.
-/

namespace OpenAI086

/-- A real 2-vector projection onto its first coordinate. -/
def rowPrefixProjection (x : ℝ × ℝ) : ℝ × ℝ := (x.1, 0)

/-- First row of a rational orthogonal transformation. -/
def rationalRowZero (x : ℝ × ℝ) : ℝ := (3 * x.1 + 4 * x.2) / 5

/-- Second row of the same rational orthogonal transformation. -/
def rationalRowOne (x : ℝ × ℝ) : ℝ := (-4 * x.1 + 3 * x.2) / 5

/-- The two row maps form a Parseval pair, satisfying exactly the row
contraction hypothesis of Lemma 3.3 (here with equality). -/
theorem rational_rows_parseval (x : ℝ × ℝ) :
    rationalRowZero x ^ 2 + rationalRowOne x ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
  dsimp [rationalRowZero, rationalRowOne]
  ring

/-- First-coordinate projection is self-adjoint with respect to the
usual real dot product. -/
theorem row_prefix_projection_selfadjoint (x y : ℝ × ℝ) :
    (rowPrefixProjection x).1 * y.1 + (rowPrefixProjection x).2 * y.2 =
      x.1 * (rowPrefixProjection y).1 + x.2 * (rowPrefixProjection y).2 := by
  simp [rowPrefixProjection]

/-- The projection is idempotent and nested below the identity. -/
theorem row_prefix_projection_idempotent (x : ℝ × ℝ) :
    rowPrefixProjection (rowPrefixProjection x) = rowPrefixProjection x := by
  rfl

/-- A completely explicit witness: the first row sees the smaller
prefix, the second row sees the larger prefix, and the resulting
squared row sum is 58/25 > 2 = ‖(1,-1)‖². -/
theorem varying_prefix_rows_need_more_than_constant_one :
    rationalRowZero (rowPrefixProjection ((1 : ℝ), -1)) ^ 2 +
      rationalRowOne ((1 : ℝ), -1) ^ 2 > (1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 := by
  norm_num [rationalRowZero, rationalRowOne, rowPrefixProjection]

end OpenAI086
