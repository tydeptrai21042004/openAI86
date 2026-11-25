import OpenAI086.PaperV46StoppingEnergy

/-! The size stopping rule of Lemma 3.4 on each path: the root is depth
zero; a new root is born precisely when the average exceeds twice the
last root's average. On a refining spatial partition these decisions are
constant on cells, as proved below. This does not yet build cut refits. -/
namespace OpenAI086

noncomputable def v46RootDepth (a : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if 2*a (v46RootDepth a n) < a (n+1) then n+1 else v46RootDepth a n

noncomputable def v46PathAverages (a : ℕ → ℝ) : ℕ → List ℝ
  | 0 => [a 0]
  | n+1 => if 2*a (v46RootDepth a n) < a (n+1) then
      a (n+1)::v46PathAverages a n else v46PathAverages a n

theorem v46_root_depth_le (a : ℕ → ℝ) (n : ℕ) : v46RootDepth a n ≤ n := by
  induction n with
  | zero => simp [v46RootDepth]
  | succ n ih =>
    rw [v46RootDepth]
    split_ifs <;> omega

theorem v46_path_nonempty (a : ℕ → ℝ) (n : ℕ) : v46PathAverages a n ≠ [] := by
  induction n with
  | zero => simp [v46PathAverages]
  | succ n ih =>
    rw [v46PathAverages]
    split_ifs <;> simp_all

theorem v46_path_head (a : ℕ → ℝ) (n : ℕ) :
    (v46PathAverages a n).headD 0 = a (v46RootDepth a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [v46PathAverages, v46RootDepth]
    split_ifs <;> simp_all

/-- The stopping rule constructs the descending doubling list rather than
assuming its existence. -/
theorem v46_path_doubling (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    V38Doubling (v46PathAverages a n) := by
  induction n with
  | zero => exact .single _ (ha 0)
  | succ n ih =>
    rw [v46PathAverages]
    split_ifs with hs
    · have hn := v46_path_nonempty a n
      have hh := v46_path_head a n
      cases he : v46PathAverages a n with
      | nil => exact (hn he).elim
      | cons b l =>
        simp only [he, List.headD_cons] at ih hh
        rw [← hh] at hs
        have hb : 0 ≤ b := by rw [hh]; exact ha _
        exact .cons _ b l hb hs.le ih
    · exact ih

/-- All current cells in a size segment have average at most twice the
segment root average. At a new root the bound follows from nonnegativity. -/
theorem v46_retained_average (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    a n ≤ 2*a (v46RootDepth a n) := by
  cases n with
  | zero => simp only [v46RootDepth]; linarith [ha 0]
  | succ n =>
    rw [v46RootDepth]
    split_ifs with hs
    · linarith [ha (n+1)]
    · exact le_of_not_gt hs

/-- When the two paths have the same averages through n, they have the
same last root and the same entire stopping list through n. -/
theorem v46_path_prefix_congr (a b : ℕ → ℝ) (n : ℕ)
    (h : ∀ j ≤ n, a j = b j) :
    v46RootDepth a n = v46RootDepth b n ∧ v46PathAverages a n = v46PathAverages b n := by
  induction n with
  | zero => simp [v46RootDepth, v46PathAverages, h 0 (by omega)]
  | succ n ih =>
    obtain ⟨hd, hl⟩ := ih (fun j hj => h j (by omega))
    have hr := h (v46RootDepth a n) (by have := v46_root_depth_le a n; omega)
    have hs := h (n+1) (by omega)
    constructor
    · simp only [v46RootDepth, ← hd, hr, hs]
    · simp only [v46PathAverages, ← hd, hr, hs, hl]

/-- Refining spatial cells have a well-defined stopping decision, not a
point-dependent choice within a cell. -/
theorem v46_spatial_stopping_cell {Ω C : Type*}
    (cell : ℕ → Ω → C) (avg : ℕ → C → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, cell j x = cell j y → cell i x = cell i y)
    (n : ℕ) (x y : Ω) (hxy : cell n x = cell n y) :
    v46RootDepth (fun j => avg j (cell j x)) n =
      v46RootDepth (fun j => avg j (cell j y)) n ∧
    v46PathAverages (fun j => avg j (cell j x)) n =
      v46PathAverages (fun j => avg j (cell j y)) n := by
  apply v46_path_prefix_congr
  intro j hj
  rw [href j n hj x y hxy]

/-- The terminal cut at the next stopping root has at most four times the
old segment average if the child average is at most twice its parent.
The dyadic equal-length child property supplies this last premise. -/
theorem v46_cut_average (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (n : ℕ) (hchild : a (n+1) ≤ 2*a n) :
    a (n+1) ≤ 4*a (v46RootDepth a n) := by
  linarith [v46_retained_average a ha n]

/-- Pointwise square sum for the actual stopping algorithm. -/
theorem v46_actual_path_square_sum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (n : ℕ) (M : ℝ) (hM : ∀ j ≤ n, a j ≤ M) :
    ((v46PathAverages a n).map (fun x => x^2)).sum ≤ (4/3 : ℝ)*M^2 := by
  have h := v46_doubling_square_sum _ (v46_path_doubling a ha n)
  rw [v46_path_head] at h
  have hm := hM _ (v46_root_depth_le a n)
  have hs : (a (v46RootDepth a n))^2 ≤ M^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm)
      (show 0 ≤ M+a (v46RootDepth a n) by linarith [ha (v46RootDepth a n)])]
  linarith

end OpenAI086
