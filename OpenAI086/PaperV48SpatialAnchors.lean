import OpenAI086.PaperV47AnchorPath

/-! V48: spatially adapted anchor states on a finite refining measurable
partition. Coefficients at level j are functions of the level-j cell;
therefore the coefficient path, and hence the last-anchor decision, is
constant on every terminal cell. This is the finite-horizon stopping-time
bridge needed before constructing the full generation-by-generation
anchor partitions of Lemma 3.4. -/
namespace OpenAI086

/-- A level-j coefficient is read from the level-j ancestor of a terminal
cell label. -/
def v48TerminalCoefficientPath {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X) (c : C) : ℕ → X :=
  fun j => coefficient j (ancestor j c)

/-- Last anchor depth determined by the finite coefficient path of a
terminal cell. -/
def v48TerminalAnchorDepth {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon : ℕ) (c : C) : ℕ :=
  v47AnchorDepth (v48TerminalCoefficientPath ancestor coefficient c)
    threshold horizon

/-- Anchor-list state at a terminal cell, including all earlier anchors. -/
def v48TerminalAnchorList {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon : ℕ) (c : C) : List ℕ :=
  v47AnchorList (v48TerminalCoefficientPath ancestor coefficient c)
    threshold horizon

/-- Spatial anchor depth is a finite-valued function of the terminal
partition atom. -/
def v48SpatialAnchorDepth {Ω C X : Type*}
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon : ℕ) (x : Ω) : ℕ :=
  v48TerminalAnchorDepth ancestor coefficient threshold horizon (cell horizon x)

/-- Spatial anchor list is also determined by the terminal atom. -/
def v48SpatialAnchorList {Ω C X : Type*}
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon : ℕ) (x : Ω) : List ℕ :=
  v48TerminalAnchorList ancestor coefficient threshold horizon (cell horizon x)

/-- A terminal cell fixes every earlier coefficient, and so fixes the
complete anchor decision up to the finite horizon. -/
theorem v48_anchor_state_constant_on_terminal_cell
    {Ω C X : Type*} (cell : ℕ → Ω → C)
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (horizon : ℕ) (hancestor : ∀ j ≤ horizon, ∀ x,
      cell j x = ancestor j (cell horizon x))
    (threshold : ℝ) (x y : Ω)
    (hxy : cell horizon x = cell horizon y) :
    v48SpatialAnchorDepth cell ancestor coefficient threshold horizon x =
      v48SpatialAnchorDepth cell ancestor coefficient threshold horizon y ∧
    v48SpatialAnchorList cell ancestor coefficient threshold horizon x =
      v48SpatialAnchorList cell ancestor coefficient threshold horizon y := by
  have hpath : ∀ j ≤ horizon,
      v48TerminalCoefficientPath ancestor coefficient (cell horizon x) j =
      v48TerminalCoefficientPath ancestor coefficient (cell horizon y) j := by
    intro j hj
    simp only [v48TerminalCoefficientPath]
    rw [hxy]
  have h := v47_anchor_prefix_congr
    (v48TerminalCoefficientPath ancestor coefficient (cell horizon x))
    (v48TerminalCoefficientPath ancestor coefficient (cell horizon y))
    threshold horizon hpath
  exact h

/-- The terminal-cell coefficient path agrees with the actual coefficient
read at each coarser spatial level. -/
theorem v48_terminal_path_matches_levels
    {Ω C X : Type*} (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (horizon : ℕ)
    (hancestor : ∀ j ≤ horizon, ∀ x,
      cell j x = ancestor j (cell horizon x)) (x : Ω) :
    ∀ j ≤ horizon,
      v48TerminalCoefficientPath ancestor coefficient (cell horizon x) j =
        coefficient j (cell j x) := by
  intro j hj
  simp [v48TerminalCoefficientPath, hancestor j hj x]

/-- A terminal anchor label consists of the stopping depth and the
spatial cell at that depth. It is constant on terminal partition atoms. -/
def v48SpatialAnchorLabel {Ω C X : Type*}
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon : ℕ) (x : Ω) : ℕ × C :=
  let n := v48SpatialAnchorDepth cell ancestor coefficient threshold horizon x
  (n, ancestor n (cell horizon x))

theorem v48_anchor_label_constant_on_terminal_cell
    {Ω C X : Type*} (cell : ℕ → Ω → C)
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (horizon : ℕ) (hancestor : ∀ j ≤ horizon, ∀ x,
      cell j x = ancestor j (cell horizon x))
    (threshold : ℝ) (x y : Ω)
    (hxy : cell horizon x = cell horizon y) :
    v48SpatialAnchorLabel cell ancestor coefficient threshold horizon x =
      v48SpatialAnchorLabel cell ancestor coefficient threshold horizon y := by
  obtain ⟨hd, _⟩ := v48_anchor_state_constant_on_terminal_cell
    cell ancestor coefficient horizon hancestor threshold x y hxy
  simp [v48SpatialAnchorLabel, hd, hxy]

/-- If terminal-cell fibres are measurable, every set on which the
spatial anchor depth has a prescribed value is measurable. This is the
finite-union measurability needed for restart roots. -/
theorem v48_anchor_depth_fiber_measurable
    {Ω C X : Type*} [MeasurableSpace Ω] [Fintype C] [DecidableEq C]
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ) (horizon depth : ℕ)
    (hm : ∀ c, MeasurableSet {x | cell horizon x = c}) :
    MeasurableSet {x | v48SpatialAnchorDepth cell ancestor coefficient
      threshold horizon x = depth} := by
  classical
  have heq : {x | v48SpatialAnchorDepth cell ancestor coefficient threshold
      horizon x = depth} =
      ⋃ c : C, if v48TerminalAnchorDepth ancestor coefficient threshold horizon c = depth
        then {x | cell horizon x = c} else ∅ := by
    ext x
    simp [v48SpatialAnchorDepth]
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  split_ifs
  · exact hm c
  · exact MeasurableSet.empty

/-- The terminal anchor-label fibres are measurable finite unions of
terminal-cell fibres. -/
theorem v48_anchor_label_fiber_measurable
    {Ω C X : Type*} [MeasurableSpace Ω] [Fintype C] [DecidableEq C]
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ) (horizon : ℕ)
    (label : ℕ × C)
    (hm : ∀ c, MeasurableSet {x | cell horizon x = c}) :
    MeasurableSet {x | v48SpatialAnchorLabel cell ancestor coefficient
      threshold horizon x = label} := by
  classical
  have heq : {x | v48SpatialAnchorLabel cell ancestor coefficient threshold
      horizon x = label} =
      ⋃ c : C, if (v48TerminalAnchorDepth ancestor coefficient threshold horizon c,
          ancestor (v48TerminalAnchorDepth ancestor coefficient threshold horizon c) c) = label
        then {x | cell horizon x = c} else ∅ := by
    ext x
    simp [v48SpatialAnchorLabel, v48SpatialAnchorDepth]
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  split_ifs
  · exact hm c
  · exact MeasurableSet.empty

/-- Each anchor-label atom is contained in the spatial cell at the
stopping depth carried by that label. -/
theorem v48_anchor_label_subset_cell
    {Ω C X : Type*} (cell : ℕ → Ω → C)
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (horizon : ℕ) (hancestor : ∀ j ≤ horizon, ∀ x,
      cell j x = ancestor j (cell horizon x))
    (threshold : ℝ) (depth : ℕ) (c : C) :
    {x | v48SpatialAnchorLabel cell ancestor coefficient threshold horizon x =
      (depth,c)} ⊆ {x | cell depth x = c} := by
  intro x hx
  have hdepth :
      v48SpatialAnchorDepth cell ancestor coefficient threshold horizon x = depth := by
    simpa [v48SpatialAnchorLabel] using congrArg Prod.fst hx
  have hcell0 :
      ancestor (v48SpatialAnchorDepth cell ancestor coefficient threshold horizon x)
        (cell horizon x) = c := by
    simpa [v48SpatialAnchorLabel] using congrArg Prod.snd hx
  have hle : depth ≤ horizon := by
    rw [← hdepth]
    exact v47_anchor_depth_le
      (v48TerminalCoefficientPath ancestor coefficient (cell horizon x)) threshold horizon
  have hspatial := hancestor depth hle x
  have hcell' : ancestor depth (cell horizon x) = c := by
    simpa [hdepth] using hcell0
  calc
    cell depth x = ancestor depth (cell horizon x) := hspatial
    _ = c := hcell'


/-- The chronological anchor depths on a terminal spatial cell. The stored
`v47AnchorList` is newest-first, so reversing it exposes generation order. -/
def v48TerminalAnchorDepths {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon : ℕ) (c : C) : List ℕ :=
  (v47AnchorList (v48TerminalCoefficientPath ancestor coefficient c)
    threshold horizon).reverse

/-- The stage-n atom label: an active anchor cell if the path has an
n-th anchor, and otherwise the terminal cut cell. The left/right tags keep
active anchors distinct from terminal atoms, exactly as in the paper's
completion of each anchor generation to a stopping partition. -/
def v48TerminalStageLabel {C X : Type*}
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon stage : ℕ) (c : C) : Sum (ℕ × C) C :=
  match (v48TerminalAnchorDepths ancestor coefficient threshold horizon c).get? stage with
  | some depth => Sum.inl (depth, ancestor depth c)
  | none => Sum.inr c

/-- Spatial version of the stage-n atom label. -/
def v48SpatialStageLabel {Ω C X : Type*}
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon stage : ℕ) (x : Ω) : Sum (ℕ × C) C :=
  v48TerminalStageLabel ancestor coefficient threshold horizon stage (cell horizon x)

/-- Every stage label is constant on a terminal partition atom. -/
theorem v48_stage_label_constant_on_terminal_cell
    {Ω C X : Type*} (cell : ℕ → Ω → C)
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (horizon stage : ℕ) (x y : Ω)
    (hxy : cell horizon x = cell horizon y) :
    v48SpatialStageLabel cell ancestor coefficient threshold horizon stage x =
      v48SpatialStageLabel cell ancestor coefficient threshold horizon stage y := by
  simp [v48SpatialStageLabel, hxy]

/-- For a finite terminal partition, every stage-label atom is measurable.
Thus each generation defines a genuine finite measurable partition; the
additional refinement relation between consecutive generations is a
separate obligation recorded in V48 progress. -/
theorem v48_stage_label_fiber_measurable
    {Ω C X : Type*} [MeasurableSpace Ω] [Fintype C] [DecidableEq C]
    (cell : ℕ → Ω → C) (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon stage : ℕ) (label : Sum (ℕ × C) C)
    (hm : ∀ c, MeasurableSet {x | cell horizon x = c}) :
    MeasurableSet {x | v48SpatialStageLabel cell ancestor coefficient
      threshold horizon stage x = label} := by
  classical
  have heq :
      {x | v48SpatialStageLabel cell ancestor coefficient threshold horizon stage x = label} =
      ⋃ c : C, if v48TerminalStageLabel ancestor coefficient threshold horizon stage c = label
        then {x | cell horizon x = c} else ∅ := by
    ext x
    simp [v48SpatialStageLabel]
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  split_ifs
  · exact hm c
  · exact MeasurableSet.empty

/-- The active label carries the actual ancestor cell at its selected
anchor depth. -/
theorem v48_stage_active_cell
    {C X : Type*} (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ)
    (horizon stage : ℕ) (leaf : C) (depth : ℕ) (anchorCell : C)
    (hlabel : v48TerminalStageLabel ancestor coefficient threshold horizon stage leaf =
      Sum.inl (depth, anchorCell)) :
    ancestor depth leaf = anchorCell := by
  unfold v48TerminalStageLabel at hlabel
  cases hget : (v48TerminalAnchorDepths ancestor coefficient threshold horizon leaf).get? stage with
  | none => simp [hget] at hlabel
  | some selectedDepth =>
      simp [hget] at hlabel
      have hd : selectedDepth = depth := congrArg Prod.fst hlabel
      have hc : ancestor selectedDepth leaf = anchorCell := congrArg Prod.snd hlabel
      rw [← hd]
      exact hc

end OpenAI086
