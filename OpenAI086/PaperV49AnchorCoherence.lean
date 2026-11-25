import OpenAI086.PaperV48AnchorPartitions

/-! V49: active-anchor cells determine their complete earlier anchor history.

The V48 history-labelled partitions were nested, but could in principle
retain distinct labels for two paths which arrive at the same current
anchor cell.  The manuscript's first-match rule rules this out: the
coefficient at every earlier depth is read from the corresponding spatial
ancestor, and that ancestor is determined by the current cell.  This file
formalizes that coherence statement and the predecessor-cell consequence.
-/
namespace OpenAI086

/-- Every selected anchor depth through `depth`, in chronological order.
The reverse compensates for `v47AnchorList`, which stores newest first. -/
def v49AnchorDepthHistory {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (depth : ℕ) (terminal : C) : List ℕ :=
  (v47AnchorList (v48TerminalCoefficientPath ancestor coefficient terminal)
    threshold depth).reverse

/-- Every anchor depth selected by the finite path lies at or above its
initial cell and no deeper than the path horizon. -/
theorem v49_anchor_list_mem_le {X : Type*} [NormedAddCommGroup X]
    (c : ℕ → X) (threshold : ℝ) (depth j : ℕ)
    (hj : j ∈ v47AnchorList c threshold depth) : j ≤ depth := by
  induction depth with
  | zero =>
      simp [v47AnchorList] at hj
      omega
  | succ n ih =>
      simp only [v47AnchorList] at hj
      split_ifs at hj with h
      · simp only [List.mem_cons] at hj
        rcases hj with hj | hj
        · subst j
          omega
        · exact (ih hj).trans (by omega)
      · exact (ih hj).trans (by omega)

/-- If two terminal cells have the same ancestor at a given depth, their
coefficient paths agree at every earlier depth. -/
theorem v49_terminal_coefficient_prefix_coherent
    {C X : Type*} (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (depth : ℕ)
    (leaf₁ leaf₂ : C)
    (hancestor : ∀ i j, i ≤ j → ∀ a b,
      ancestor j a = ancestor j b → ancestor i a = ancestor i b)
    (hcell : ancestor depth leaf₁ = ancestor depth leaf₂) :
    ∀ j ≤ depth,
      v48TerminalCoefficientPath ancestor coefficient leaf₁ j =
        v48TerminalCoefficientPath ancestor coefficient leaf₂ j := by
  intro j hj
  simp only [v48TerminalCoefficientPath]
  exact congrArg (coefficient j) (hancestor j depth hj leaf₁ leaf₂ hcell)

/-- The actual selected-anchor depth history through a current anchor cell
is independent of which terminal descendant is used to represent it. -/
theorem v49_anchor_depth_history_coherent
    {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ) (depth : ℕ)
    (leaf₁ leaf₂ : C)
    (hancestor : ∀ i j, i ≤ j → ∀ a b,
      ancestor j a = ancestor j b → ancestor i a = ancestor i b)
    (hcell : ancestor depth leaf₁ = ancestor depth leaf₂) :
    v49AnchorDepthHistory ancestor coefficient threshold depth leaf₁ =
      v49AnchorDepthHistory ancestor coefficient threshold depth leaf₂ := by
  unfold v49AnchorDepthHistory
  have hpath := v49_terminal_coefficient_prefix_coherent
    ancestor coefficient depth leaf₁ leaf₂ hancestor hcell
  have hlist := v47_anchor_prefix_congr
    (v48TerminalCoefficientPath ancestor coefficient leaf₁)
    (v48TerminalCoefficientPath ancestor coefficient leaf₂)
    threshold depth hpath
  rw [hlist.2]

/-- The complete list of earlier anchor cells, not only their depths, is
also determined by the current anchor cell. -/
def v49AnchorCellHistory {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (depth : ℕ) (terminal : C) : List (ℕ × C) :=
  (v49AnchorDepthHistory ancestor coefficient threshold depth terminal).map
    (fun j => (j, ancestor j terminal))

theorem v49_anchor_cell_history_coherent
    {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C)
    (coefficient : ℕ → C → X) (threshold : ℝ) (depth : ℕ)
    (leaf₁ leaf₂ : C)
    (hancestor : ∀ i j, i ≤ j → ∀ a b,
      ancestor j a = ancestor j b → ancestor i a = ancestor i b)
    (hcell : ancestor depth leaf₁ = ancestor depth leaf₂) :
    v49AnchorCellHistory ancestor coefficient threshold depth leaf₁ =
      v49AnchorCellHistory ancestor coefficient threshold depth leaf₂ := by
  unfold v49AnchorCellHistory
  rw [v49_anchor_depth_history_coherent ancestor coefficient threshold depth
    leaf₁ leaf₂ hancestor hcell]
  apply List.map_congr_left
  intro j hj
  have hj' : j ∈ v47AnchorList
      (v48TerminalCoefficientPath ancestor coefficient leaf₂) threshold depth := by
    simpa [v49AnchorDepthHistory] using hj
  have hjle := v49_anchor_list_mem_le
    (v48TerminalCoefficientPath ancestor coefficient leaf₂) threshold depth j hj'
  exact congrArg (fun c => (j, c))
    (hancestor j depth hjle leaf₁ leaf₂ hcell)

/-- The immediately preceding anchor on a path, represented by its depth
and spatial cell. At depth zero the initial root is its own predecessor. -/
def v49PreviousAnchorLabel {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (depth : ℕ) (terminal : C) : ℕ × C :=
  if depth = 0 then (0, ancestor 0 terminal)
  else
    let p := v47AnchorDepth
      (v48TerminalCoefficientPath ancestor coefficient terminal)
      threshold (depth - 1)
    (p, ancestor p terminal)

/-- An active anchor cell determines the preceding anchor cell. This is
the coherence fact needed to quotient V48's history-labelled partition
to the paper's exact active-anchor atoms. -/
theorem v49_previous_anchor_label_coherent
    {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (depth : ℕ) (leaf₁ leaf₂ : C)
    (hancestor : ∀ i j, i ≤ j → ∀ a b,
      ancestor j a = ancestor j b → ancestor i a = ancestor i b)
    (hcell : ancestor depth leaf₁ = ancestor depth leaf₂) :
    v49PreviousAnchorLabel ancestor coefficient threshold depth leaf₁ =
      v49PreviousAnchorLabel ancestor coefficient threshold depth leaf₂ := by
  by_cases hzero : depth = 0
  · simp [v49PreviousAnchorLabel, hzero, hcell]
  · have hpos : 0 < depth := Nat.pos_of_ne_zero hzero
    let n := depth - 1
    have hsucc : n + 1 = depth := by
      dsimp [n]
      omega
    have hpath : ∀ j ≤ n,
        v48TerminalCoefficientPath ancestor coefficient leaf₁ j =
          v48TerminalCoefficientPath ancestor coefficient leaf₂ j := by
      intro j hj
      exact v49_terminal_coefficient_prefix_coherent
        ancestor coefficient depth leaf₁ leaf₂ hancestor hcell j (by omega)
    have hprefix := v47_anchor_prefix_congr
      (v48TerminalCoefficientPath ancestor coefficient leaf₁)
      (v48TerminalCoefficientPath ancestor coefficient leaf₂)
      threshold n hpath
    have hdepth :
        v47AnchorDepth (v48TerminalCoefficientPath ancestor coefficient leaf₁)
          threshold n =
        v47AnchorDepth (v48TerminalCoefficientPath ancestor coefficient leaf₂)
          threshold n := hprefix.1
    have hple : v47AnchorDepth
        (v48TerminalCoefficientPath ancestor coefficient leaf₁) threshold n ≤ n :=
      v47_anchor_depth_le _ _ _
    have hprevCell := hancestor
      (v47AnchorDepth (v48TerminalCoefficientPath ancestor coefficient leaf₁)
        threshold n) depth (by omega) leaf₁ leaf₂ hcell
    simp [v49PreviousAnchorLabel, hzero, n, hdepth, hprevCell]

/-- The predecessor coherence statement in terms of equality of active
anchor labels. -/
theorem v49_active_anchor_label_determines_predecessor
    {C X : Type*} [NormedAddCommGroup X]
    (ancestor : ℕ → C → C) (coefficient : ℕ → C → X)
    (threshold : ℝ) (depth : ℕ) (leaf₁ leaf₂ : C)
    (hancestor : ∀ i j, i ≤ j → ∀ a b,
      ancestor j a = ancestor j b → ancestor i a = ancestor i b)
    (hlabel : (depth, ancestor depth leaf₁) =
      (depth, ancestor depth leaf₂)) :
    v49PreviousAnchorLabel ancestor coefficient threshold depth leaf₁ =
      v49PreviousAnchorLabel ancestor coefficient threshold depth leaf₂ := by
  exact v49_previous_anchor_label_coherent ancestor coefficient threshold depth
    leaf₁ leaf₂ hancestor (congrArg Prod.snd hlabel)

end OpenAI086
