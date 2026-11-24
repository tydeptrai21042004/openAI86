import Mathlib

/-! Lemma 3.4, p.10: maximal inequality for finite weighted refining
partitions. This is a finite weighted proof of the L² maximal constant 2,
not a proof for arbitrary Bochner L² inputs on the real dyadic lattice.
The proof uses running maxima rather than a distribution-function integral. -/
namespace OpenAI086

variable {Ω C : Type*} [Fintype Ω] [Fintype C]

def v37RunningMax (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, x => max (v37RunningMax a n x) (a n x)

theorem v37_max_nonneg (a : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ v37RunningMax a n x := by
  induction n with
  | zero => simp [v37RunningMax]
  | succ n ih => exact ih.trans (le_max_left _ _)

/-- The square increment of a running maximum is bounded by twice the
current value times the (nonnegative) maximum increment. -/
theorem v37_max_square_step (u b : ℝ) (hu : 0 ≤ u) :
    (max u b)^2-u^2 ≤ 2*b*(max u b-u) := by
  rcases le_total b u with h | h
  · rw [max_eq_left h]; simp
  · rw [max_eq_right h]; nlinarith [sq_nonneg (b-u)]

/-- Running maxima through level n are constant on every finer cell. -/
theorem v37_max_adapted (cell : ℕ → Ω → C) (avg : ℕ → C → ℝ)
    (href : ∀ i j, i ≤ j → ∀ x y, cell j x = cell j y → cell i x = cell i y)
    (n j : ℕ) (hn : n ≤ j+1) (x y : Ω) (he : cell j x = cell j y) :
    v37RunningMax (fun i t => avg i (cell i t)) n x =
    v37RunningMax (fun i t => avg i (cell i t)) n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [v37RunningMax]
    rw [ih (by omega), href n j (by omega) x y he]

/-- Finite cellwise moment identities imply the identity with every test
constant on those cells. No bound on the number of cells is involved. -/
theorem v37_weighted_cell_moment [DecidableEq C]
    (cell : Ω → C) (w f a b : Ω → ℝ)
    (hm : ∀ c : C,
      (∑ x, if cell x = c then w x*a x else 0) =
      ∑ x, if cell x = c then w x*f x else 0)
    (hb : ∀ x y, cell x = cell y → b x = b y) :
    (∑ x, w x*a x*b x) = ∑ x, w x*f x*b x := by
  classical
  let t : C → ℝ := fun c => if h : ∃ x, cell x = c then b (Classical.choose h) else 0
  have ht (x : Ω) : t (cell x) = b x := by
    unfold t
    rw [dif_pos (show ∃ y, cell y = cell x from ⟨x,rfl⟩)]
    exact hb _ x (Classical.choose_spec _)
  have expand (g : Ω → ℝ) :
      (∑ x, w x*g x*b x) = ∑ c : C, (∑ x, if cell x = c then w x*g x else 0)*t c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp [ite_mul, ht]
  rw [expand a, expand f]
  exact Finset.sum_congr rfl (fun c _ => by rw [hm c])

/-- L² maximal inequality from the exact finite conditional-average moment
identities. The weight can be zero at individual points. -/
theorem v37_weighted_maximal_L2 [DecidableEq C]
    (cell : ℕ → Ω → C) (avg : ℕ → C → ℝ) (w f : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (href : ∀ i j, i ≤ j → ∀ x y, cell j x = cell j y → cell i x = cell i y)
    (hm : ∀ n c, (∑ x, if cell n x = c then w x*avg n c else 0) =
      ∑ x, if cell n x = c then w x*f x else 0)
    (N : ℕ) :
    (∑ x, w x*(v37RunningMax (fun n x => avg n (cell n x)) N x)^2) ≤
      4*(∑ x, w x*(f x)^2) := by
  classical
  let a : ℕ → Ω → ℝ := fun n x => avg n (cell n x)
  let M : ℕ → Ω → ℝ := v37RunningMax a
  have main (n : ℕ) : (∑ x, w x*(M n x)^2) ≤ 2*(∑ x, w x*f x*M n x) := by
    induction n with
    | zero => simp [M, v37RunningMax]
    | succ n ih =>
      let b : Ω → ℝ := fun x => M (n+1) x-M n x
      have hba (x y : Ω) (he : cell n x = cell n y) : b x = b y := by
        dsimp [b,M,a]
        rw [v37_max_adapted cell avg href (n+1) n (by omega) x y he,
            v37_max_adapted cell avg href n n (by omega) x y he]
      have hma : ∀ c, (∑ x, if cell n x = c then w x*a n x else 0) =
          ∑ x, if cell n x = c then w x*f x else 0 := by
        intro c
        calc
          _ = ∑ x, if cell n x = c then w x*avg n c else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases h : cell n x = c <;> simp [h,a]
          _ = _ := hm n c
      have he := v37_weighted_cell_moment (cell n) w f (a n) b hma hba
      have hs : (∑ x, w x*(M (n+1) x)^2) ≤
          ∑ x, (w x*(M n x)^2+2*(w x*a n x*b x)) := by
        apply Finset.sum_le_sum
        intro x _
        have h := v37_max_square_step (M n x) (a n x) (v37_max_nonneg a n x)
        change (M (n+1) x)^2-(M n x)^2 ≤ 2*a n x*b x at h
        nlinarith [mul_le_mul_of_nonneg_left h (hw x)]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
      rw [he] at hs
      have hsplit : (∑ x, w x*f x*M (n+1) x) =
          (∑ x, w x*f x*M n x)+(∑ x, w x*f x*b x) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by dsimp [b]; ring)
      rw [hsplit]
      linarith
  have hpoint : (∑ x, 2*(w x*f x*M N x)) ≤
      ∑ x, (w x*(M N x)^2/2+2*(w x*(f x)^2)) := by
    apply Finset.sum_le_sum
    intro x _
    have h : 0 ≤ (M N x-2*f x)^2 := sq_nonneg _
    nlinarith [mul_nonneg (hw x) h]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_div] at hpoint
  have h := main N
  change (∑ x, w x*(M N x)^2) ≤ 4*(∑ x, w x*(f x)^2)
  linarith

/-- The actual normalized weighted cell average (zero on zero-mass cells). -/
noncomputable def v37CellAverage [DecidableEq C] (cell : ℕ → Ω → C)
    (w f : Ω → ℝ) (n : ℕ) (c : C) : ℝ :=
  (∑ x, if cell n x = c then w x*f x else 0) /
    (∑ x, if cell n x = c then w x else 0)

/-- The cellwise moment identities are proved for the actual average,
including zero-mass cells. -/
theorem v37_average_moment [DecidableEq C] (cell : ℕ → Ω → C)
    (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (n : ℕ) (c : C) :
    (∑ x, if cell n x = c then w x*v37CellAverage cell w f n c else 0) =
    ∑ x, if cell n x = c then w x*f x else 0 := by
  classical
  let mass : ℝ := ∑ x, if cell n x = c then w x else 0
  let moment : ℝ := ∑ x, if cell n x = c then w x*f x else 0
  have hfactor : (∑ x, if cell n x = c then w x*v37CellAverage cell w f n c else 0) =
      mass*v37CellAverage cell w f n c := by
    dsimp [mass]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : cell n x = c <;> simp [hx]
  rw [hfactor]
  change mass*(moment/mass) = moment
  by_cases hm : mass = 0
  · have hz (x : Ω) (hx : cell n x = c) : w x = 0 := by
      have hle : (if cell n x = c then w x else 0) ≤ mass :=
        Finset.single_le_sum (fun y _ => by split_ifs <;> first | exact hw y | exact le_rfl) (Finset.mem_univ x)
      rw [if_pos hx, hm] at hle
      exact le_antisymm hle (hw x)
    have hmom : moment = 0 := by
      dsimp [moment]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : cell n x = c
      · simp [hx, hz x hx]
      · simp [hx]
    simp [hmom]
  · field_simp [hm]

/-- Unconditional finite weighted maximal estimate for the normalized
cell-average construction. No martingale identity is assumed. -/
theorem v37_actual_weighted_maximal_L2 [DecidableEq C]
    (cell : ℕ → Ω → C) (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (href : ∀ i j, i ≤ j → ∀ x y, cell j x = cell j y → cell i x = cell i y)
    (N : ℕ) :
    (∑ x, w x*(v37RunningMax (fun n x => v37CellAverage cell w f n (cell n x)) N x)^2) ≤
      4*(∑ x, w x*(f x)^2) :=
  v37_weighted_maximal_L2 cell (v37CellAverage cell w f) w f hw href
    (v37_average_moment cell w f hw) N

end OpenAI086
