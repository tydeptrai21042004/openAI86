import OpenAI086.PaperV48SpatialAnchors

/-! V48: finite anchor-history partitions. At generation n, a terminal path
is labelled either by its first n+1 anchor cells (if it is still active), or
by its complete history together with its terminal cut cell. These labels
form a nested finite family of measurable partitions. This history-labelled
partition is a refinement of the paper's active-anchor partition; identifying
when two equal current anchor cells have identical prior histories is a
separate quotient/coherence obligation. -/
namespace OpenAI086
open MeasureTheory

/-- A history-labelled partition atom at a specified anchor generation.
The right summand records a path that has already terminated. -/
def v48HistoryStageLabel {α C : Type*}
    (history : List α) (terminal : C) (stage : ℕ) :
    Sum (List α) (List α × C) :=
  if stage < history.length then
    Sum.inl (history.take (stage+1))
  else
    Sum.inr (history, terminal)

/-- The history-labelled partitions are nested: equality at generation
n+1 forces equality at generation n. The proof is purely finite and does
not assume any commutation or geometric property. -/
theorem v48_history_stage_refines
    {α C : Type*} (history₁ : List α) (terminal₁ : C)
    (history₂ : List α) (terminal₂ : C) (stage : ℕ)
    (heq : v48HistoryStageLabel history₁ terminal₁ (stage+1) =
      v48HistoryStageLabel history₂ terminal₂ (stage+1)) :
    v48HistoryStageLabel history₁ terminal₁ stage =
      v48HistoryStageLabel history₂ terminal₂ stage := by
  by_cases h₁ : stage+1 < history₁.length
  · by_cases h₂ : stage+1 < history₂.length
    · have hprefix :
          history₁.take (stage+1+1) = history₂.take (stage+1+1) := by
        simpa [v48HistoryStageLabel, h₁, h₂] using heq
      have hprefix' :
          history₁.take (stage+1) = history₂.take (stage+1) := by
        have h := congrArg (fun xs : List α => xs.take (stage+1)) hprefix
        simpa [List.take_take, Nat.min_eq_left (by omega : stage+1 ≤ stage+1+1)] using h
      have h₁' : stage < history₁.length := by omega
      have h₂' : stage < history₂.length := by omega
      simp [v48HistoryStageLabel, h₁', h₂', hprefix']
    · simp [v48HistoryStageLabel, h₁, h₂] at heq
  · by_cases h₂ : stage+1 < history₂.length
    · simp [v48HistoryStageLabel, h₁, h₂] at heq
    · have hpair : (history₁, terminal₁) = (history₂, terminal₂) := by
        simpa [v48HistoryStageLabel, h₁, h₂] using heq
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      rfl

/-- The chronological list of selected anchor depths, paired with their
actual spatial ancestor cells. -/
def v48TerminalAnchorHistory {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon : ℕ) (terminal : C) : List (ℕ × C) :=
  (v48TerminalAnchorDepths ancestor coefficient threshold horizon terminal).map
    (fun depth => (depth, ancestor depth terminal))

/-- The stage partition label attached to a terminal cell. -/
def v48TerminalPartitionStageLabel {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon stage : ℕ) (terminal : C) :
    Sum (List (ℕ × C)) (List (ℕ × C) × C) :=
  v48HistoryStageLabel
    (v48TerminalAnchorHistory ancestor coefficient threshold horizon terminal)
    terminal stage

/-- Spatial realization of the terminal-history partition label. -/
def v48SpatialPartitionStageLabel {Ω C X : Type*}
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon stage : ℕ) (x : Ω) :
    Sum (List (ℕ × C)) (List (ℕ × C) × C) :=
  v48TerminalPartitionStageLabel ancestor coefficient threshold horizon stage
    (cell horizon x)

/-- The spatial history partitions refine from stage n+1 to stage n. -/
theorem v48_spatial_partition_refines
    {Ω C X : Type*} (cell : ℕ → Ω → C)
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon stage : ℕ) (x y : Ω)
    (heq : v48SpatialPartitionStageLabel cell ancestor coefficient threshold
      horizon (stage+1) x =
      v48SpatialPartitionStageLabel cell ancestor coefficient threshold
        horizon (stage+1) y) :
    v48SpatialPartitionStageLabel cell ancestor coefficient threshold
      horizon stage x =
    v48SpatialPartitionStageLabel cell ancestor coefficient threshold
      horizon stage y := by
  exact v48_history_stage_refines
    (v48TerminalAnchorHistory ancestor coefficient threshold horizon (cell horizon x))
    (cell horizon x)
    (v48TerminalAnchorHistory ancestor coefficient threshold horizon (cell horizon y))
    (cell horizon y) stage heq

/-- Each history-partition atom is measurable when the finite terminal
cell fibres are measurable. -/
theorem v48_spatial_partition_fiber_measurable
    {Ω C X : Type*} [MeasurableSpace Ω] [Fintype C] [DecidableEq C]
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon stage : ℕ)
    (label : Sum (List (ℕ × C)) (List (ℕ × C) × C))
    (hm : ∀ c, MeasurableSet {x | cell horizon x = c}) :
    MeasurableSet {x | v48SpatialPartitionStageLabel cell ancestor coefficient
      threshold horizon stage x = label} := by
  classical
  have heq :
      {x | v48SpatialPartitionStageLabel cell ancestor coefficient threshold
        horizon stage x = label} =
      ⋃ c : C, if v48TerminalPartitionStageLabel ancestor coefficient threshold
          horizon stage c = label
        then {x | cell horizon x = c} else ∅ := by
    ext x
    simp [v48SpatialPartitionStageLabel]
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  split_ifs
  · exact hm c
  · exact MeasurableSet.empty


/-- The spatial history partition has finite range because its label
factors through the finite set of terminal cells. -/
theorem v48_spatial_partition_range_finite
    {Ω C X : Type*} [Fintype C]
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon stage : ℕ) :
    (Set.range (v48SpatialPartitionStageLabel cell ancestor coefficient
      threshold horizon stage)).Finite := by
  classical
  apply (Set.finite_range (fun c : C =>
    v48TerminalPartitionStageLabel ancestor coefficient threshold horizon stage c)).subset
  rintro label ⟨x, rfl⟩
  exact ⟨cell horizon x, rfl⟩

end OpenAI086
