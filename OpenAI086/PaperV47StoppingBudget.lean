import OpenAI086.PaperV47MeasuredMaximal
import OpenAI086.PaperV46StoppingConstruction

/-! Integrate the actual stopping rule on the finite terminal partition.
The resulting cost counts a stopping ancestor once on each point of its
support, and hence weights it by the mass of that support. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

/-- Whether the original size-stopping algorithm selects depth n. -/
def v47SizeStop (a : ℕ → ℝ) : ℕ → Prop
  | 0 => True
  | n+1 => 2*a (v46RootDepth a n) < a (n+1)

/-- The stopping-list energy is exactly the sum over selected depths;
this identity prevents double-counting a retained root at later depths. -/
theorem v47_stopping_cost_identity (a : ℕ → ℝ) (n : ℕ) :
    ((v46PathAverages a n).map (fun b => b^2)).sum =
      ∑ j ∈ Finset.range (n+1), if v47SizeStop a j then (a j)^2 else 0 := by
  classical
  induction n with
  | zero => simp [v46PathAverages,v47SizeStop]
  | succ n ih =>
    rw [Finset.sum_range_succ, v46PathAverages]
    simp only [v47SizeStop]
    split_ifs <;> simp [ih,add_comm]

/-- Measured stopping-root budget. The integral of the path list energy
is at most 16/3 of the input squared integral. The root tree must be
represented by positive-length measurable terminal cells and nested
ancestors. The integrand is cell-constant, not a discretization of f. -/
theorem v47_measured_stopping_budget {Ω Q C : Type*} [MeasurableSpace Ω]
    [Fintype Q] [DecidableEq Q] [Fintype C] [DecidableEq C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (cell : Ω → Q)
    (hm : ∀ q, MeasurableSet {x | cell x = q})
    (ancestor : ℕ → Q → C)
    (href : ∀ i j, i ≤ j → ∀ x y, ancestor j x = ancestor j y → ancestor i x = ancestor i y)
    (f : Ω → ℝ) (hf : Integrable f μ) (hs : Integrable (fun x => (f x)^2) μ)
    (hn : ∀ x, 0 ≤ f x) (N : ℕ) :
    (∫ x, ((v46PathAverages (fun j => v37CellAverage ancestor
      (fun q => (μ {y | cell y = q}).toReal) (v47LeafMean μ cell f)
      j (ancestor j (cell x))) N).map (fun a => a^2)).sum ∂μ) ≤
      (16/3 : ℝ)*(∫ x, (f x)^2 ∂μ) := by
  let w : Q → ℝ := fun q => (μ {x | cell x = q}).toReal
  let b := v47LeafMean μ cell f
  let a : ℕ → Q → ℝ := fun j q => v37CellAverage ancestor w b j (ancestor j q)
  let M := v37RunningMax a (N+1)
  have hb (q : Q) : 0 ≤ b q := by
    apply div_nonneg (integral_nonneg hn) ENNReal.toReal_nonneg
  have ha (j : ℕ) (q : Q) : 0 ≤ a j q := by
    dsimp [a,v37CellAverage]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro i _
      split_ifs <;> first | exact mul_nonneg ENNReal.toReal_nonneg (hb i) | exact le_rfl
    · apply Finset.sum_nonneg
      intro i _
      split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
  let F : Q → ℝ := fun q => ((v46PathAverages (fun j => a j q) N).map (fun x => x^2)).sum
  have hpoint (q : Q) : F q ≤ (4/3 : ℝ)*(M q)^2 :=
    v46_actual_path_square_sum (fun j => a j q) (fun j => ha j q) N (M q)
      (fun j hj => v47_running_max_ge a (N+1) j (by omega) q)
  have hM := v47_measured_maximal_L2 μ cell hm ancestor href f hf hs (N+1)
  change (∫ x, (M (cell x))^2 ∂μ) ≤ _ at hM
  rw [v47_integral_cell_constant μ cell hm (fun q => (M q)^2)] at hM
  change (∫ x, F (cell x) ∂μ) ≤ _
  rw [v47_integral_cell_constant μ cell hm F]
  calc
    _ ≤ ∑ q, w q*((4/3 : ℝ)*(M q)^2) :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hpoint q) ENNReal.toReal_nonneg)
    _ = (4/3 : ℝ)*(∑ q, w q*(M q)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ _ := by linarith

end OpenAI086
