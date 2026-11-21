import Mathlib

/-!
# Lemma 3.5: the one-dimensional coefficient-ratio mechanism

The full height-bins lemma (PDF pages 13--14) uses rational linear
relations in arbitrary finite dimension and a count of occupied dyadic
bins. Here we verify the entire elementary ratio step for one real
frequency and coefficient magnitudes in `[1/B, B]`.

For nonzero rationals of height at most `B`, this coefficient condition
follows from the numerator/denominator bounds. Its conclusion is the
`B²` width of the unique logarithmic cluster in dimension one.

This does not establish the full multi-dimensional Lemma 3.5.
-/

namespace OpenAI086

/-- A bounded coefficient and a coefficient bounded below by `1/B`
produce outputs within multiplicative factor `B²`, regardless of how
large or small the unrestricted real frequency `ξ` is. -/
theorem one_dim_height_ratio
    (B a b ξ : ℝ) (hB : 1 ≤ B)
    (ha : |a| ≤ B) (hb : 1 / B ≤ |b|) :
    |a * ξ| ≤ B ^ 2 * |b * ξ| := by
  have hBpos : 0 < B := by linarith
  have hmul : 1 ≤ B * |b| := by
    exact (div_le_iff₀ hBpos).mp hb
  have hscale : B ≤ B ^ 2 * |b| := by
    calc
      B = B * 1 := by ring
      _ ≤ B * (B * |b|) :=
        mul_le_mul_of_nonneg_left hmul (le_of_lt hBpos)
      _ = B ^ 2 * |b| := by ring
  calc
    |a * ξ| = |a| * |ξ| := abs_mul a ξ
    _ ≤ (B ^ 2 * |b|) * |ξ| :=
      mul_le_mul_of_nonneg_right (ha.trans hscale) (abs_nonneg ξ)
    _ = B ^ 2 * |b * ξ| := by rw [abs_mul]; ring

/-- Any two coefficients in the same height-budget range yield
comparable evaluations in *both* directions, even when `ξ = 0`. -/
theorem one_dim_height_ratio_symmetric
    (B a b ξ : ℝ) (hB : 1 ≤ B)
    (ha0 : 1 / B ≤ |a|) (ha1 : |a| ≤ B)
    (hb0 : 1 / B ≤ |b|) (hb1 : |b| ≤ B) :
    |a * ξ| ≤ B ^ 2 * |b * ξ| ∧
      |b * ξ| ≤ B ^ 2 * |a * ξ| := by
  exact ⟨one_dim_height_ratio B a b ξ hB ha1 hb0,
         one_dim_height_ratio B b a ξ hB hb1 ha0⟩

end OpenAI086
