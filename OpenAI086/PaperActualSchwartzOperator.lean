import OpenAI086.PaperSchwartzSpatialL1

/-! Concrete L¹-valued trilinear Schwartz operator and exact extension bridge.
The sole substantive hypothesis of the final bridge is the uniform norm
estimate; the proof of that estimate itself remains open. Source candidate. -/
noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology

def v25ActualL1 (a b c : V25S) : V24L1 :=
  v25ToL1 a b c (v25_T_memLp a b c)

theorem v25_actual_L1_ae (a b c : V25S) :
    (fun x => v25ActualL1 a b c x) =ᵐ[volume] v25T a b c :=
  v25_L1_ae a b c (v25_T_memLp a b c)

theorem v25_L1_add_1 (a b c d : V25S) :
    v25ActualL1 (a+d) b c = v25ActualL1 a b c + v25ActualL1 d b c := by
  apply Lp.ext
  filter_upwards [v25_actual_L1_ae (a+d) b c, v25_actual_L1_ae a b c,
    v25_actual_L1_ae d b c, Lp.coeFn_add (v25ActualL1 a b c) (v25ActualL1 d b c)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  change v25T (a+d) b c x = v25ActualL1 a b c x + v25ActualL1 d b c x
  rw [h₂,h₃]
  exact v25_T_add_1 a b c d x

theorem v25_L1_smul_1 (a b c : V25S) (r : ℂ) :
    v25ActualL1 (r • a) b c = r • v25ActualL1 a b c := by
  apply Lp.ext
  filter_upwards [v25_actual_L1_ae (r • a) b c, v25_actual_L1_ae a b c,
    Lp.coeFn_smul r (v25ActualL1 a b c)] with x h₁ h₂ h₃
  rw [h₁,h₃]
  change v25T (r • a) b c x = r • v25ActualL1 a b c x
  rw [h₂]
  exact v25_T_smul_1 a b c r x

theorem v25_L1_add_2 (a b c d : V25S) :
    v25ActualL1 a (b+d) c = v25ActualL1 a b c + v25ActualL1 a d c := by
  apply Lp.ext
  filter_upwards [v25_actual_L1_ae a (b+d) c, v25_actual_L1_ae a b c,
    v25_actual_L1_ae a d c, Lp.coeFn_add (v25ActualL1 a b c) (v25ActualL1 a d c)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  change v25T a (b+d) c x = v25ActualL1 a b c x + v25ActualL1 a d c x
  rw [h₂,h₃]
  exact v25_T_add_2 a b c d x

theorem v25_L1_smul_2 (a b c : V25S) (r : ℂ) :
    v25ActualL1 a (r • b) c = r • v25ActualL1 a b c := by
  apply Lp.ext
  filter_upwards [v25_actual_L1_ae a (r • b) c, v25_actual_L1_ae a b c,
    Lp.coeFn_smul r (v25ActualL1 a b c)] with x h₁ h₂ h₃
  rw [h₁,h₃]
  change v25T a (r • b) c x = r • v25ActualL1 a b c x
  rw [h₂]
  exact v25_T_smul_2 a b c r x

theorem v25_L1_add_3 (a b c d : V25S) :
    v25ActualL1 a b (c+d) = v25ActualL1 a b c + v25ActualL1 a b d := by
  apply Lp.ext
  filter_upwards [v25_actual_L1_ae a b (c+d), v25_actual_L1_ae a b c,
    v25_actual_L1_ae a b d, Lp.coeFn_add (v25ActualL1 a b c) (v25ActualL1 a b d)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  change v25T a b (c+d) x = v25ActualL1 a b c x + v25ActualL1 a b d x
  rw [h₂,h₃]
  exact v25_T_add_3 a b c d x

theorem v25_L1_smul_3 (a b c : V25S) (r : ℂ) :
    v25ActualL1 a b (r • c) = r • v25ActualL1 a b c := by
  apply Lp.ext
  filter_upwards [v25_actual_L1_ae a b (r • c), v25_actual_L1_ae a b c,
    Lp.coeFn_smul r (v25ActualL1 a b c)] with x h₁ h₂ h₃
  rw [h₁,h₃]
  change v25T a b (r • c) x = r • v25ActualL1 a b c x
  rw [h₂]
  exact v25_T_smul_3 a b c r x

def v25SchwartzOperator : V24SchwartzOperator where
  toFun a := {
    toFun b := {
      toFun c := v25ActualL1 a b c
      map_add' c d := v25_L1_add_3 a b c d
      map_smul' r c := v25_L1_smul_3 a b c r }
    map_add' b d := by ext c; exact v25_L1_add_2 a b c d
    map_smul' r b := by ext c; exact v25_L1_smul_2 a b c r }
  map_add' a d := by ext b c; exact v25_L1_add_1 a b c d
  map_smul' r a := by ext b c; exact v25_L1_smul_1 a b c r

theorem v25_actual_realization : V24PVRealization v25SchwartzOperator := by
  intro f
  refine ⟨v25T (f 0) (f 1) (f 2), v25_T_pv f, ?_⟩
  exact (v25_actual_L1_ae (f 0) (f 1) (f 2)).symm

/-- If the central uniform estimate is proved for this actual Schwartz
operator, the original main theorem and unique bounded extension follow. -/
theorem v25_main_and_extension (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ a b c, ‖v25SchwartzOperator a b c‖ ≤ C * ‖v24SchwartzEmbedding a‖ *
        ‖v24SchwartzEmbedding b‖ * ‖v24SchwartzEmbedding c‖) :
    Theorem1_1_Goal ∧ (∃! S : V24BoundedOperator,
      (∀ a b c, S (v24SchwartzEmbedding a) (v24SchwartzEmbedding b)
        (v24SchwartzEmbedding c) = v25SchwartzOperator a b c) ∧ ‖S‖ ≤ C) :=
  v24_main_and_extension v25SchwartzOperator C hC v25_actual_realization hT

end OpenAI086
