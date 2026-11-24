import Mathlib

/-! Lemma 7.1, p.53: exact change of exponents after taking the qth power.
Uses genuine iterated Lebesgue integrals, including infinite magnitudes.
The weighted scalar maximal theorem and the two extrapolations remain open. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped ENNReal

def v25Magnitude {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ℝ) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x, (f x)^p ∂μ) ^ (1/p)

theorem v25_magnitude_power {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (f : α → ℝ≥0∞) :
    v25Magnitude μ (p/q) (fun x => (f x)^q) = (v25Magnitude μ p f)^q := by
  unfold v25Magnitude
  have h1 : q*(p/q) = p := by field_simp
  have h2 : 1/(p/q) = (1/p)*q := by field_simp
  simp_rw [← ENNReal.rpow_mul, h1, h2]

def v25MixedMagnitude {Y X W : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    [MeasurableSpace W] (μY : Measure Y) (μX : Measure X) (μW : Measure W)
    (p b h : ℝ) (f : Y → X → W → ℝ≥0∞) : ℝ≥0∞ :=
  v25Magnitude μY p (fun y => v25Magnitude μX b (fun x => v25Magnitude μW h (f y x)))

theorem v25_mixed_magnitude_power {Y X W : Type*} [MeasurableSpace Y]
    [MeasurableSpace X] [MeasurableSpace W] (μY : Measure Y) (μX : Measure X) (μW : Measure W)
    (p b h q : ℝ) (hp : 0 < p) (hb : 0 < b) (hh : 0 < h) (hq : 0 < q)
    (f : Y → X → W → ℝ≥0∞) :
    v25MixedMagnitude μY μX μW (p/q) (b/q) (h/q) (fun y x w => (f y x w)^q) =
      (v25MixedMagnitude μY μX μW p b h f)^q := by
  unfold v25MixedMagnitude
  simp_rw [v25_magnitude_power μW h q hh hq, v25_magnitude_power μX b q hb hq,
    v25_magnitude_power μY p q hp hq]

end OpenAI086
