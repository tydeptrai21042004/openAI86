import OpenAI086.PaperCompressionMaximal
import OpenAI086.PaperCompressionMeasureBridge

/-! Continuous finite-depth maximal estimate (Lemma 3.4, p.10).
The final measurable partition is represented by a finite-valued cell map.
Integrals, not point samples, define its weights and means. The running
maximum on a coarser partition is exactly a function on these terminal
atoms. No approximation of the input by point samples is used. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

section Measure
variable {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q] [DecidableEq Q]

/-- Integration over a finite measurable partition given by its cell map. -/
theorem v47_integral_partition (μ : Measure Ω) (cell : Ω → Q)
    (hm : ∀ q, MeasurableSet {x | cell x = q})
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∑ q, ∫ x in {x | cell x = q}, f x ∂μ := by
  classical
  have he : (fun x => f x) = fun x => ∑ q, ({y | cell y = q} : Set Ω).indicator f x := by
    funext x
    rw [Finset.sum_eq_single (cell x)]
    · simp
    · intro q _ hq
      exact Set.indicator_of_notMem (by simpa [eq_comm] using hq) _
    · simp
  calc
    _ = ∫ x, ∑ q, ({y | cell y = q} : Set Ω).indicator f x ∂μ := by rw [← he]
    _ = ∑ q, ∫ x, ({y | cell y = q} : Set Ω).indicator f x ∂μ :=
      integral_finset_sum _ (fun q _ => hf.integrable_indicator (hm q))
    _ = _ := Finset.sum_congr rfl (fun q _ => integral_indicator (hm q))

/-- Exact integral of a finite cell-constant function. -/
theorem v47_integral_cell_constant (μ : Measure Ω) [IsFiniteMeasure μ]
    (cell : Ω → Q) (hm : ∀ q, MeasurableSet {x | cell x = q}) (b : Q → ℝ) :
    (∫ x, b (cell x) ∂μ) = ∑ q, (μ {x | cell x = q}).toReal*b q := by
  classical
  have he : (fun x => b (cell x)) =
      fun x => ∑ q, ({y | cell y = q} : Set Ω).indicator (fun _ => b q) x := by
    funext x
    rw [Finset.sum_eq_single (cell x)]
    · simp
    · intro q _ hq
      exact Set.indicator_of_notMem (by simpa [eq_comm] using hq) _
    · simp
  rw [he, integral_finset_sum _ (fun q _ => (integrable_const (b q)).integrable_indicator (hm q))]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_indicator (hm q), integral_const]
  simp [Measure.real, smul_eq_mul]

/-- Jensen for an unnormalized finite measure, including the zero-mass case. -/
theorem v47_weighted_jensen (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hs : Integrable (fun x => (f x)^2) μ) :
    (μ Set.univ).toReal * ((∫ x, f x ∂μ)/(μ Set.univ).toReal)^2 ≤
      ∫ x, (f x)^2 ∂μ := by
  let w := (μ Set.univ).toReal
  let b := (∫ x, f x ∂μ)/w
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  by_cases h : w = 0
  · change w*b^2 ≤ _
    rw [h, zero_mul]
    exact integral_nonneg (fun x => sq_nonneg (f x))
  · have hnon : 0 ≤ ∫ x, (f x)^2-2*b*f x+b^2 ∂μ :=
      integral_nonneg (fun x => by nlinarith [sq_nonneg (f x-b)])
    rw [integral_add (hs.sub (hf.const_mul (2*b))) (integrable_const (b^2)),
      integral_sub hs (hf.const_mul (2*b)), integral_const_mul, integral_const] at hnon
    simp only [Measure.real, smul_eq_mul] at hnon
    change 0 ≤ (∫ x, (f x)^2 ∂μ)-2*b*(∫ x, f x ∂μ)+w*b^2 at hnon
    have he : w*b = ∫ x, f x ∂μ := by dsimp [b]; field_simp [h]
    rw [← he] at hnon
    change w*b^2 ≤ _
    linarith only [hnon, show (2*b*(w*b):ℝ) = 2*(w*b^2) by ring]

/-- Terminal means computed from Lebesgue/Bochner integrals (real scalar
input, in particular f = ‖z‖). -/
def v47LeafMean (μ : Measure Ω) (cell : Ω → Q) (f : Ω → ℝ) (q : Q) : ℝ :=
  (∫ x in {x | cell x = q}, f x ∂μ)/(μ {x | cell x = q}).toReal

/-- Actual finite-depth running maximal function on a measurable tree.
`ancestor n q` identifies the level-n ancestor of terminal atom q.
The coarse means are length-weighted terminal means, not point samples. -/
def v47MeasuredMax {C : Type*} [DecidableEq C] (μ : Measure Ω)
    (cell : Ω → Q) (ancestor : ℕ → Q → C) (f : Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  v37RunningMax (fun n q => v37CellAverage ancestor
    (fun q => (μ {y | cell y = q}).toReal) (v47LeafMean μ cell f) n (ancestor n q)) N (cell x)

/-- The continuous finite-depth L² maximal estimate, with exact squared
constant four. No maximal-function inequality is assumed. -/
theorem v47_measured_maximal_L2 {C : Type*} [Fintype C] [DecidableEq C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (cell : Ω → Q)
    (hm : ∀ q, MeasurableSet {x | cell x = q})
    (ancestor : ℕ → Q → C)
    (href : ∀ i j, i ≤ j → ∀ x y, ancestor j x = ancestor j y → ancestor i x = ancestor i y)
    (f : Ω → ℝ) (hf : Integrable f μ) (hs : Integrable (fun x => (f x)^2) μ) (N : ℕ) :
    (∫ x, (v47MeasuredMax μ cell ancestor f N x)^2 ∂μ) ≤ 4*(∫ x, (f x)^2 ∂μ) := by
  let w : Q → ℝ := fun q => (μ {x | cell x = q}).toReal
  let b := v47LeafMean μ cell f
  let M := v37RunningMax (fun n q => v37CellAverage ancestor w b n (ancestor n q)) N
  have hJ : (∑ q, w q*(b q)^2) ≤ ∫ x, (f x)^2 ∂μ := by
    rw [v47_integral_partition μ cell hm _ hs]
    apply Finset.sum_le_sum
    intro q _
    have hj := v47_weighted_jensen (μ.restrict {x | cell x = q}) f
      hf.integrableOn hs.integrableOn
    simpa [w,b,v47LeafMean, Measure.restrict_apply MeasurableSet.univ] using hj
  have hM := v37_actual_weighted_maximal_L2 ancestor w b
    (fun _ => ENNReal.toReal_nonneg) href N
  change (∑ q, w q*(M q)^2) ≤ 4*(∑ q, w q*(b q)^2) at hM
  change (∫ x, (M (cell x))^2 ∂μ) ≤ _
  rw [v47_integral_cell_constant μ cell hm (fun q => (M q)^2)]
  exact hM.trans (mul_le_mul_of_nonneg_left hJ (by norm_num))

/-- The integral on a coarse cell is the sum over its actual terminal
atoms. This identifies the finite weighted representation with the
continuous spatial averages. -/
theorem v47_coarse_integral {C : Type*} [DecidableEq C]
    (μ : Measure Ω) (cell : Ω → Q)
    (hm : ∀ q, MeasurableSet {x | cell x = q})
    (parent : Q → C) (c : C) (f : Ω → ℝ) (hf : Integrable f μ)
    (hc : MeasurableSet {x | parent (cell x) = c}) :
    (∫ x in {x | parent (cell x) = c}, f x ∂μ) =
      ∑ q, if parent q = c then (∫ x in {x | cell x = q}, f x ∂μ) else 0 := by
  classical
  let A : Set Ω := {x | parent (cell x) = c}
  have he : A.indicator f = fun x => ∑ q,
      if parent q = c then ({y | cell y = q} : Set Ω).indicator f x else 0 := by
    funext x
    rw [Finset.sum_eq_single (cell x)]
    · by_cases h : parent (cell x) = c <;> simp [A,h]
    · intro q _ hq
      by_cases h : parent q = c
      · rw [if_pos h, Set.indicator_of_notMem]
        exact fun hx => hq (by simpa [eq_comm] using hx)
      · simp [h]
    · simp
  rw [← integral_indicator hc]
  change (∫ x, A.indicator f x ∂μ) = _
  rw [he, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q _
    by_cases h : parent q = c
    · simp only [h, if_true]
      exact integral_indicator (hm q)
    · simp [h]
  · intro q _
    by_cases h : parent q = c
    · simpa [h] using hf.integrable_indicator (hm q)
    · simp [h]

/-- For positive-length terminal atoms, weighted ancestor means are
exactly the normalized integral on the ancestor. -/
theorem v47_coarse_average {C : Type*} [DecidableEq C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (cell : Ω → Q)
    (hm : ∀ q, MeasurableSet {x | cell x = q})
    (hpos : ∀ q, 0 < (μ {x | cell x = q}).toReal)
    (ancestor : ℕ → Q → C) (n : ℕ) (c : C) (f : Ω → ℝ)
    (hf : Integrable f μ) (hc : MeasurableSet {x | ancestor n (cell x) = c}) :
    v37CellAverage ancestor (fun q => (μ {x | cell x = q}).toReal)
      (v47LeafMean μ cell f) n c =
      (∫ x in {x | ancestor n (cell x) = c}, f x ∂μ) /
        (μ {x | ancestor n (cell x) = c}).toReal := by
  unfold v37CellAverage
  have hnum : (∑ q, if ancestor n q = c then
      (μ {x | cell x = q}).toReal * v47LeafMean μ cell f q else 0) =
      ∫ x in {x | ancestor n (cell x) = c}, f x ∂μ := by
    rw [v47_coarse_integral μ cell hm (ancestor n) c f hf hc]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : ancestor n q = c
    · simp only [h, if_true, v47LeafMean]
      field_simp [(hpos q).ne'] <;> ring
    · simp [h]
  have hden : (∑ q, if ancestor n q = c then (μ {x | cell x = q}).toReal else 0) =
      (μ {x | ancestor n (cell x) = c}).toReal := by
    have hh := v47_coarse_integral μ cell hm (ancestor n) c (fun _ => (1:ℝ))
      (integrable_const 1) hc
    simpa [integral_const, Measure.real, smul_eq_mul] using hh.symm
  rw [hnum,hden]

/-- Pointwise upper bound for every average included in the running max. -/
theorem v47_running_max_ge (a : ℕ → Q → ℝ) (n j : ℕ) (hj : j < n) (q : Q) :
    a j q ≤ v37RunningMax a n q := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [v37RunningMax]
    by_cases h : j = n
    · subst j; exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

end Measure
end OpenAI086
