import OpenAI086.PaperCompressionEnergySplit

/-! Quantitative path estimates in Lemma 3.4, p.10–11. The list is the
actual sequence of positive stopping averages along a fixed path, read
from deepest to shallowest. The construction of the spatial tree and
its connection to these lists are still separate obligations. -/
namespace OpenAI086

/-- The square sum of a descending doubling chain is at most 4/3 times
its largest square. This is the pointwise stopping-average bound. -/
theorem v46_doubling_square_sum (l : List ℝ) (h : V38Doubling l) :
    (l.map (fun a => a^2)).sum ≤ (4/3 : ℝ)*(l.headD 0)^2 := by
  induction h with
  | nil => simp
  | single a ha => simp <;> nlinarith [sq_nonneg a]
  | cons a b l hb hab h ih =>
    simp only [List.map_cons, List.sum_cons, List.headD_cons] at ih ⊢
    have ha : 0 ≤ a := by linarith
    have hab2 : 4*b^2 ≤ a^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a+2*b by linarith)]
    linarith

/-- Every member of a descending doubling chain is bounded by its head. -/
theorem v46_doubling_member_le (l : List ℝ) (h : V38Doubling l) :
    ∀ a ∈ l, a ≤ l.headD 0 := by
  induction h with
  | nil => simp
  | single a ha => simp
  | cons a b l hb hab h ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_rfl
    · exact (ih x hx).trans (by simp only [List.headD_cons]; linarith)

/-- Sum only the entries strictly below a threshold. -/
noncomputable def v46LowSum (t : ℝ) : List ℝ → ℝ
  | [] => 0
  | a::l => (if a < t then a else 0) + v46LowSum t l

/-- Count entries at or above a threshold. -/
noncomputable def v46HighCount (t : ℝ) : List ℝ → ℕ
  | [] => 0
  | a::l => (if t ≤ a then 1 else 0) + v46HighCount t l

theorem v46_low_all (t : ℝ) (l : List ℝ) (h : ∀ x ∈ l, x < t) :
    v46LowSum t l = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [v46LowSum, if_pos (h a (by simp)), List.sum_cons,
      ih (fun x hx => h x (by simp [hx]))]

theorem v46_high_none (t : ℝ) (l : List ℝ) (h : ∀ x ∈ l, x < t) :
    v46HighCount t l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [v46HighCount, if_neg (not_le.mpr (h a (by simp))),
      ih (fun x hx => h x (by simp [hx])), Nat.zero_add]

/-- Low stopping roots have total average at most twice the threshold,
regardless of the number of roots above or below it. -/
theorem v46_low_sum_bound (l : List ℝ) (h : V38Doubling l)
    (t : ℝ) (ht : 0 ≤ t) : v46LowSum t l ≤ 2*t := by
  induction h with
  | nil => simp [v46LowSum, ht]
  | single a ha =>
    simp only [v46LowSum, add_zero]
    split_ifs <;> linarith
  | cons a b l hb hab h ih =>
    by_cases ha : a < t
    · have hall : ∀ x ∈ a::b::l, x < t := by
        intro x hx
        exact lt_of_le_of_lt (v46_doubling_member_le _ (.cons a b l hb hab h) x hx) ha
      rw [v46_low_all t _ hall]
      have hs := v38_doubling_sum _ (.cons a b l hb hab h)
      simp only [List.headD_cons] at hs
      linarith
    · simpa only [v46LowSum, if_neg ha, zero_add] using ih

/-- A nonempty high part of length n has a largest member at least
2^(n-1)t. No logarithm or integer rounding is assumed. -/
theorem v46_high_power (l : List ℝ) (h : V38Doubling l) (t : ℝ) (ht : 0 < t) :
    v46HighCount t l = 0 ∨
      2^(v46HighCount t l-1)*t ≤ l.headD 0 := by
  induction h with
  | nil => exact Or.inl rfl
  | single a ha =>
    by_cases hh : t ≤ a
    · right; simpa [v46HighCount, hh] using hh
    · left; simp [v46HighCount, hh]
  | cons a b l hb hab h ih =>
    by_cases ha : t ≤ a
    · right
      change (2:ℝ)^(v46HighCount t (a::b::l)-1)*t ≤ a
      rw [v46HighCount, if_pos ha]
      rcases ih with hz | hp
      · rw [hz]; simpa using ha
      · by_cases hn : v46HighCount t (b::l) = 0
        · rw [hn]; simpa using ha
        · have he : 1 + v46HighCount t (b::l) - 1 =
              (v46HighCount t (b::l)-1)+1 := by omega
          rw [he, pow_succ]
          simp only [List.headD_cons] at hp
          linarith
    · left
      apply v46_high_none
      intro x hx
      exact lt_of_le_of_lt (v46_doubling_member_le _ (.cons a b l hb hab h) x hx)
        (lt_of_not_ge ha)

/-- Explicit logarithmic bound for the number of high roots, even when
there are arbitrarily many small stopping averages. -/
theorem v46_high_log_bound (l : List ℝ) (h : V38Doubling l)
    (t M : ℝ) (ht : 0 < t) (hM : t ≤ M) (hhead : l.headD 0 ≤ M) :
    (v46HighCount t l : ℝ) ≤ 1 + Real.log (M/t)/Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 1 ≤ M/t := (le_div_iff₀ ht).2 (by simpa using hM)
  have hlog : 0 ≤ Real.log (M/t) := Real.log_nonneg hratio
  rcases v46_high_power l h t ht with hz | hp
  · rw [hz, Nat.cast_zero]
    linarith [div_nonneg hlog hlog2.le]
  · by_cases hn : v46HighCount t l = 0
    · rw [hn, Nat.cast_zero]
      linarith [div_nonneg hlog hlog2.le]
    · have hpow : (2:ℝ)^(v46HighCount t l-1) ≤ M/t :=
        (le_div_iff₀ ht).2 (hp.trans hhead)
      have hlogp := Real.log_le_log (show 0 < (2:ℝ)^(v46HighCount t l-1) by positivity) hpow
      rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ v46HighCount t l), Nat.cast_one] at hlogp
      have hh := (le_div_iff₀ hlog2).2 hlogp
      linarith

/-- At the paper's threshold M/(G D²), the two estimates have precisely
its low-average and logarithmic high-multiplicity dependence. -/
theorem v46_paper_path_split (l : List ℝ) (h : V38Doubling l)
    (M D G : ℝ) (hM : 0 < M) (hD : 2 ≤ D) (hG : G = 4*D^5)
    (hhead : l.headD 0 ≤ M) :
    G*v46LowSum (M/(G*D^2)) l ≤ 2*M/D^2 ∧
    (v46HighCount (M/(G*D^2)) l : ℝ) ≤ 3+7*Real.log D/Real.log 2 := by
  have hDp : 0 < D := by linarith
  have hGp : 0 < G := by rw [hG]; positivity
  have hden : 0 < G*D^2 := by positivity
  have hden1 : 1 ≤ G*D^2 := by
    have hd1 : 1 ≤ D := by linarith
    have hd5 : 1 ≤ D^5 := one_le_pow₀ hd1 _
    have hd2 : 1 ≤ D^2 := one_le_pow₀ hd1 _
    rw [hG]
    nlinarith [mul_le_mul hd5 hd2 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ D^5)]
  let t := M/(G*D^2)
  have ht : 0 < t := div_pos hM hden
  have htM : t ≤ M := (div_le_iff₀ hden).2 (by
    simpa using mul_le_mul_of_nonneg_left hden1 hM.le)
  constructor
  · have hh := mul_le_mul_of_nonneg_left (v46_low_sum_bound l h t ht.le) hGp.le
    calc
      _ ≤ G*(2*t) := hh
      _ = 2*M/D^2 := by dsimp [t]; field_simp [hGp.ne', hDp.ne'] <;> ring
  · have hh := v46_high_log_bound l h t M ht htM hhead
    have he : M/t = G*D^2 := by dsimp [t]; field_simp [hM.ne', hGp.ne', hDp.ne']
    rw [he, hG, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (pow_ne_zero _ hDp.ne'),
      Real.log_pow, Real.log_pow] at hh
    have h4 : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [h4] at hh
    change (v46HighCount t l : ℝ) ≤ _
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    convert hh using 1 <;> field_simp [hl] <;> ring

end OpenAI086
