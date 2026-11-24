import Mathlib

/-! Lemma 2.4: actual compactly supported bounded tests recover the L¹
norm of an integrable complex output. No uniform four-linear estimate is
assumed implicitly; it is the explicit hypothesis of the reduction. -/
noncomputable section
namespace OpenAI086
open MeasureTheory Filter Set Topology

/-- Bilinear (not sesquilinear) testing phase. Division at zero is total. -/
def v28TestPhase (z : ℂ) : ℂ := star z / (‖z‖ : ℂ)

theorem v28_test_phase_bound (z : ℂ) : ‖v28TestPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz, v28TestPhase]
  · rw [v28TestPhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z)]
    change ‖(starRingEnd ℂ) z‖ / ‖z‖ ≤ 1
    rw [Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz)]

theorem v28_test_phase_exact (z : ℂ) : v28TestPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, v28TestPhase]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [v28TestPhase, div_mul_eq_mul_div]
    change (starRingEnd ℂ z * z) / (‖z‖ : ℂ) = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp [hn]

/-- Test on the whole interval, then extend by zero. -/
def v28CompactTest (g : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  (Icc (-(n : ℝ)) (n : ℝ)).indicator (fun x => v28TestPhase (g x))

theorem v28_compact_test_bound (g : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    ‖v28CompactTest g n x‖ ≤ 1 := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simpa [v28CompactTest, Set.indicator_of_mem hx] using v28_test_phase_bound (g x)
  · simp [v28CompactTest, Set.indicator_of_not_mem hx]

theorem v28_compact_test_measurable (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    Measurable (v28CompactTest g n) := by
  apply Measurable.indicator _ measurableSet_Icc
  unfold v28TestPhase
  fun_prop

theorem v28_compact_test_zero (g : ℝ → ℂ) (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (-(n : ℝ)) (n : ℝ)) : v28CompactTest g n x = 0 := by
  simp [v28CompactTest, Set.indicator_of_not_mem hx]

theorem v28_compact_test_pair (g : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    v28CompactTest g n x * g x =
      (Icc (-(n : ℝ)) (n : ℝ)).indicator (fun x => (‖g x‖ : ℂ)) x := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simpa [v28CompactTest, Set.indicator_of_mem hx] using v28_test_phase_exact (g x)
  · simp [v28CompactTest, Set.indicator_of_not_mem hx]

/-- Ordinary L¹ norm is recovered by bounded tests of compact support.
The cutoff exhaustion is proved, not an assumed norming-functional fact. -/
theorem v28_compact_testing_L1 (g : ℝ → ℂ) (hg : Integrable g) (hm : Measurable g)
    (B : ℝ) (htest : ∀ f : ℝ → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ 1) →
      (∃ n : ℕ, ∀ x ∉ Icc (-(n : ℝ)) (n : ℝ), f x = 0) →
      ‖∫ x, f x * g x‖ ≤ B) : (∫ x, ‖g x‖) ≤ B := by
  let F : ℕ → ℝ → ℝ := fun n =>
    (Icc (-(n : ℝ)) (n : ℝ)).indicator (fun x => ‖g x‖)
  have hF : ∀ n, Integrable (F n) := fun n => hg.norm.indicator measurableSet_Icc
  have hlim : Tendsto (fun n => ∫ x, F n x) atTop (𝓝 (∫ x, ‖g x‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    · exact fun n => (hF n).aestronglyMeasurable
    · exact hg.norm
    · intro n; filter_upwards [] with x
      by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ) <;>
        simp [F, Set.indicator, hx, abs_of_nonneg (norm_nonneg (g x))]
    · filter_upwards [] with x
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm'
      have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm'
      have hx : x ∈ Icc (-(m : ℝ)) (m : ℝ) := by
        rw [mem_Icc, ← abs_le]; linarith
      simp [F, Set.indicator_of_mem hx]
  apply le_of_tendsto hlim
  filter_upwards [] with n
  have htestn := htest (v28CompactTest g n) (v28_compact_test_measurable g hm n)
    (v28_compact_test_bound g n) ⟨n, v28_compact_test_zero g n⟩
  have hp : (fun x => v28CompactTest g n x * g x) = fun x => (F n x : ℂ) := by
    funext x
    rw [v28_compact_test_pair]
    by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ) <;> simp [F, Set.indicator, hx]
  rw [hp, integral_complex_ofReal, Complex.norm_real] at htestn
  exact (le_abs_self _).trans htestn

end OpenAI086
