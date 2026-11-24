import OpenAI086.PaperHeightVectorAssembly

/-! Exact finite qualifying sets and supremum-family wrappers for the
corrected Lemma 3.5. These are source proof candidates, not certificates.
The frequency vector is unrestricted. No bounded scale horizon is assumed. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators ENNReal

/-- Logarithmic coordinate of a positive magnitude at an arbitrary integer depth. -/
theorem v36_log_scaled (r v : ℝ) (l : ℕ) (n : ℤ)
    (hr : 0 < r) (hv : 0 < v) :
    Real.log (v35Scale r l n * v) =
      (l : ℝ) * (Real.log r - (n : ℝ) * Real.log 2) + Real.log v := by
  have hs : 0 < r * (2 : ℝ)^(-n) := mul_pos hr (zpow_pos (by norm_num) _)
  unfold v35Scale
  rw [Real.log_mul (pow_ne_zero _ hs.ne') hv.ne', Real.log_pow,
    Real.log_mul hr.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  push_cast <;> ring

def v36ScaleLo (r β v : ℝ) (l : ℕ) : ℝ :=
  ((l : ℝ)*Real.log r + Real.log v - Real.log β)/((l : ℝ)*Real.log 2)

def v36ScaleHi (r α v : ℝ) (l : ℕ) : ℝ :=
  ((l : ℝ)*Real.log r + Real.log v - Real.log α)/((l : ℝ)*Real.log 2)

/-- Exact interval of qualifying depths for a single positive value. -/
theorem v36_scale_iff_window (r α β v : ℝ) (l : ℕ) (n : ℤ)
    (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hv : 0 < v) (hl : 0 < l) :
    (α ≤ v35Scale r l n*v ∧ v35Scale r l n*v ≤ β) ↔
      (v36ScaleLo r β v l ≤ (n : ℝ) ∧ (n : ℝ) ≤ v36ScaleHi r α v l) := by
  have hb : 0 < β := hα.trans_le hαβ
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl' : (0:ℝ) < l := by exact_mod_cast hl
  have hden : 0 < (l:ℝ)*Real.log 2 := mul_pos hl' h2
  have hs : 0 < v35Scale r l n*v := by unfold v35Scale; positivity
  have he := v36_log_scaled r v l n hr hv
  constructor
  · rintro ⟨ha, hb'⟩
    have h1 := Real.log_le_log hα ha
    have h3 := Real.log_le_log hs hb'
    rw [he] at h1 h3
    unfold v36ScaleLo v36ScaleHi
    refine ⟨(div_le_iff₀ hden).mpr ?_, (le_div_iff₀ hden).mpr ?_⟩ <;> nlinarith
  · rintro ⟨ha, hb'⟩
    unfold v36ScaleLo v36ScaleHi at ha hb'
    have h1 := (div_le_iff₀ hden).mp ha
    have h3 := (le_div_iff₀ hden).mp hb'
    constructor
    · apply (Real.log_le_log_iff hα hs).mp
      rw [he]
      nlinarith
    · apply (Real.log_le_log_iff hs hb).mp
      rw [he]
      nlinarith

/-- Enumerates *all* qualifying integer scales as a union of exact
integer windows. The positive value set, not a grid of scales, is finite. -/
def v36Qualifying (E : Finset ℝ) (r α β : ℝ) (l : ℕ) : Finset ℤ := by
  classical
  exact E.biUnion (fun v => Finset.Icc (Int.ceil (v36ScaleLo r β v l))
    (Int.floor (v36ScaleHi r α v l)))

theorem v36_mem_qualifying (E : Finset ℝ) (r α β : ℝ) (l : ℕ) (n : ℤ)
    (hE : ∀ v ∈ E, 0 < v) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    n ∈ v36Qualifying E r α β l ↔
      ∃ v ∈ E, α ≤ v35Scale r l n*v ∧ v35Scale r l n*v ≤ β := by
  classical
  unfold v36Qualifying
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hn⟩
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    exact ⟨v, hv, (v36_scale_iff_window r α β v l n hr hα hαβ (hE v hv) hl).mpr
      ⟨Int.ceil_le.mp hlo, Int.le_floor.mp hhi⟩⟩
  · rintro ⟨v, hv, ha, hb⟩
    obtain ⟨hlo, hhi⟩ := (v36_scale_iff_window r α β v l n hr hα hαβ (hE v hv) hl).mp ⟨ha,hb⟩
    exact ⟨v, hv, Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hlo, Int.le_floor.mpr hhi⟩⟩

/-- Full set finiteness, not just a bound for chosen finite subsets. -/
theorem v36_qualifying_finite (E : Finset ℝ) (r α β : ℝ) (l : ℕ)
    (hE : ∀ v ∈ E, 0 < v) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    {n : ℤ | ∃ v ∈ E, α ≤ v35Scale r l n*v ∧ v35Scale r l n*v ≤ β}.Finite := by
  classical
  have he : {n : ℤ | ∃ v ∈ E, α ≤ v35Scale r l n*v ∧ v35Scale r l n*v ≤ β} =
      (↑(v36Qualifying E r α β l) : Set ℤ) := by
    ext n
    exact (v36_mem_qualifying E r α β l n hE hr hα hαβ hl).symm
  rw [he]
  exact Finset.finite_toSet _

/-- Corrected scalar count for any subfamily of the actual height values,
with the complete qualifying set enumerated. -/
theorem v36_height_subfamily_count (d B l : ℕ) (ξ : Fin d → ℝ)
    (E : Finset ℝ) (hE : ∀ v ∈ E, v34HeightValue d B ξ v)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    ((v36Qualifying E r α β l).card : ℝ) ≤ (d : ℝ)*((2*v34Width d B +
      (Real.log β - Real.log α)/Real.log 2)/(l : ℝ)+1) := by
  apply v34_height_scale_count d B l ξ r α β hr hα hαβ hl
  intro n hn
  obtain ⟨v,hv,hlo,hhi⟩ := (v36_mem_qualifying E r α β l n
    (fun v hv => (hE v hv).1) hr hα hαβ hl).mp hn
  exact ⟨v,hE v hv,hlo,hhi⟩

theorem v36_actual_qualifying_count (d B l : ℕ) (ξ : Fin d → ℝ)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    ((v36Qualifying (v34Values d B ξ) r α β l).card : ℝ) ≤ (d : ℝ)*((2*v34Width d B +
      (Real.log β - Real.log α)/Real.log 2)/(l : ℝ)+1) :=
  v36_height_subfamily_count d B l ξ _ (fun v hv => (v34_mem_values d B ξ v).mp hv)
    r α β hr hα hαβ hl

/-- A finite family supremum is the maximum of the magnitudes and zero.
The insertion makes the empty-family convention explicit. -/
def v36SupMagnitude (F : Finset ℝ) : ℝ := by
  classical
  exact (insert 0 F).max' (by simp)

theorem v36_sup_nonneg (F : Finset ℝ) : 0 ≤ v36SupMagnitude F := by
  classical
  apply Finset.le_max'
  simp

theorem v36_sup_mem (F : Finset ℝ) (h : 0 < v36SupMagnitude F) :
    v36SupMagnitude F ∈ F := by
  classical
  have hm := Finset.max'_mem (insert 0 F) (by simp)
  change v36SupMagnitude F ∈ insert 0 F at hm
  rcases Finset.mem_insert.mp hm with hz | hf
  · exact (h.ne' hz).elim
  · exact hf

/-- For any (possibly infinite) index family of finite sets of positive
height magnitudes or zeros, all positive suprema occur in the original
finite evaluation set. No bound on the number of families is needed. -/
def v36SupValues {I : Type*} (d B : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ) : Finset ℝ := by
  classical
  exact (v34Values d B ξ).filter (fun v => ∃ i, v36SupMagnitude (F i) = v)

theorem v36_mem_sup_values {I : Type*} (d B : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ)
    (hF : ∀ i, ∀ v ∈ F i, v = 0 ∨ v34HeightValue d B ξ v) (v : ℝ) :
    v ∈ v36SupValues d B ξ F ↔ 0 < v ∧ ∃ i, v36SupMagnitude (F i) = v := by
  classical
  unfold v36SupValues
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hv, hi⟩
    exact ⟨((v34_mem_values d B ξ v).mp hv).1, hi⟩
  · rintro ⟨hv,i,hi⟩
    have hs : 0 < v36SupMagnitude (F i) := by rw [hi]; exact hv
    have hm : v ∈ F i := by rw [← hi]; exact v36_sup_mem (F i) hs
    rcases hF i v hm with hz | hval
    · exact (hv.ne' hz).elim
    · exact ⟨(v34_mem_values d B ξ v).mpr hval, i, hi⟩

theorem v36_sup_value_height {I : Type*} (d B : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ)
    (v : ℝ) (hv : v ∈ v36SupValues d B ξ F) : v34HeightValue d B ξ v := by
  classical
  exact (v34_mem_values d B ξ v).mp (Finset.mem_filter.mp hv).1

/-- Part (1) for suprema, including the occupied-bin estimate. -/
theorem v36_sup_log_bins {I : Type*} (d B : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ)
    (hF : ∀ i, ∀ v ∈ F i, v = 0 ∨ v34HeightValue d B ξ v) :
    (∃ P : Finset ℝ, P.card ≤ d ∧ ∀ i, 0 < v36SupMagnitude (F i) →
      ∃ p ∈ P, |Real.log (v36SupMagnitude (F i))/Real.log 2-p| ≤ v34Width d B) ∧
    (((v36SupValues d B ξ F).image v35Bin).card : ℝ) ≤ (d:ℝ)*(2*v34Width d B+2) := by
  classical
  constructor
  · obtain ⟨P,hp,hc⟩ := v34_height_log_cover d B ξ
    refine ⟨P,hp,?_⟩
    intro i hi
    apply hc
    exact v36_sup_value_height d B ξ F _ ((v36_mem_sup_values d B ξ F hF _).mpr ⟨hi,i,rfl⟩)
  · have hsub : (v36SupValues d B ξ F).image v35Bin ⊆ v34HeightBins d B ξ := by
      intro n hn
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
      have hval := (v34_mem_values d B ξ v).mpr (v36_sup_value_height d B ξ F v hv)
      unfold v34HeightBins v34LogValues
      exact Finset.mem_image.mpr ⟨Real.log v/Real.log 2,Finset.mem_image.mpr ⟨v,hval,rfl⟩,rfl⟩
    have hc : (((v36SupValues d B ξ F).image v35Bin).card : ℝ) ≤ (v34HeightBins d B ξ).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (v34_height_bin_count d B ξ)

/-- Exact scale predicate stated in terms of the original family indices. -/
theorem v36_sup_mem_qualifying {I : Type*} (d B l : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ)
    (hF : ∀ i, ∀ v ∈ F i, v = 0 ∨ v34HeightValue d B ξ v)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) (n : ℤ) :
    n ∈ v36Qualifying (v36SupValues d B ξ F) r α β l ↔
    ∃ i, α ≤ v35Scale r l n*v36SupMagnitude (F i) ∧ v35Scale r l n*v36SupMagnitude (F i) ≤ β := by
  classical
  rw [v36_mem_qualifying _ _ _ _ _ _ (fun v hv => (v36_sup_value_height d B ξ F v hv).1) hr hα hαβ hl]
  constructor
  · rintro ⟨v,hv,ha,hb⟩
    obtain ⟨_,i,hi⟩ := (v36_mem_sup_values d B ξ F hF v).mp hv
    exact ⟨i,by rw [hi]; exact ha,by rw [hi]; exact hb⟩
  · rintro ⟨i,ha,hb⟩
    have hs : 0 < v35Scale r l n := by unfold v35Scale; positivity
    have hv : 0 < v36SupMagnitude (F i) := pos_of_mul_pos_left (hα.trans_le ha) hs.le
    exact ⟨_,(v36_mem_sup_values d B ξ F hF _).mpr ⟨hv,i,rfl⟩,ha,hb⟩

/-- Part (2): complete finite set of qualifying suprema scales, with the
necessary dimension factor in the log-window term. -/
theorem v36_sup_scale_count {I : Type*} (d B l : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    ((v36Qualifying (v36SupValues d B ξ F) r α β l).card : ℝ) ≤ (d:ℝ)*((2*v34Width d B+
      (Real.log β-Real.log α)/Real.log 2)/(l:ℝ)+1) :=
  v36_height_subfamily_count d B l ξ _ (v36_sup_value_height d B ξ F) r α β hr hα hαβ hl

/-- Part (3) for suprema: genuine summability, not the real tsum alone. -/
theorem v36_sup_real_tail {I : Type*} (d B : ℕ) (ξ : Fin d → ℝ) (F : I → Finset ℝ)
    (hF : ∀ i, ∀ v ∈ F i, v = 0 ∨ v34HeightValue d B ξ v)
    (r ε : ℝ) (l : ℕ) (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2) :
    Summable (v35TailMax (v36SupValues d B ξ F) r l ε) ∧
    (∑' n : ℤ, v35TailMax (v36SupValues d B ξ F) r l ε n) ≤
      (d:ℝ)*(2*v34Width d B+2)*(4*ε) := by
  apply v35_real_series_of_bound
  · intro n; exact v35_tail_nonneg _ _ _ _ _
  · have hw := v34_width_nonneg d B; positivity
  · apply (v35_tail_infinite _ r ε l hr hε hl
      (fun v hv => (v36_sup_value_height d B ξ F v hv).1)).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (v36_sup_log_bins d B ξ F hF).2 (by positivity))

/-- Exact vector-family qualifying set (each vector is allowed at most h coordinates,
with shorter vectors represented by zero padding). -/
theorem v36_vector_mem_qualifying {I : Type*} [Fintype I] (h l : ℕ) (a : I → Fin h → ℝ)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) (n : ℤ) :
    n ∈ v36Qualifying (v35VectorValues h a) r α β l ↔
      ∃ i, α ≤ v35Scale r l n*v35VectorNorm h (a i) ∧ v35Scale r l n*v35VectorNorm h (a i) ≤ β := by
  classical
  rw [v36_mem_qualifying _ _ _ _ _ _ (fun v hv => (Finset.mem_filter.mp hv).2) hr hα hαβ hl]
  constructor
  · rintro ⟨v,hv,ha,hb⟩
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hv).1
    exact ⟨i,by rw [hi]; exact ha,by rw [hi]; exact hb⟩
  · rintro ⟨i,ha,hb⟩
    have hs : 0 < v35Scale r l n := by unfold v35Scale; positivity
    have hv : 0 < v35VectorNorm h (a i) := pos_of_mul_pos_left (hα.trans_le ha) hs.le
    exact ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hv⟩,ha,hb⟩

theorem v36_vector_full_scale_count {I : Type*} [Fintype I] (d B h l : ℕ)
    (ξ : Fin d → ℝ) (a : I → Fin h → ℝ) (hh : 1 ≤ h)
    (ha : ∀ i j, a i j = 0 ∨ v34HeightValue d B ξ |a i j|)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    ((v36Qualifying (v35VectorValues h a) r α β l).card : ℝ) ≤ (d:ℝ)*((2*v34Width d B+
      Real.log (h:ℝ)/(2*Real.log 2)+(Real.log β-Real.log α)/Real.log 2)/(l:ℝ)+1) := by
  apply v35_vector_scale_count d B h l ξ a hh ha r α β hr hα hαβ hl
  intro n hn
  exact (v36_vector_mem_qualifying h l a r α β hr hα hαβ hl n).mp hn

/-- The scalar sup-family tail really is the least nonnegative upper
bound of the eligible scaled suprema, including the case of no positive
eligible supremum. This proves correspondence to the original family,
not merely a bound on a derived finite set. -/
theorem v36_sup_tail_characterization {I : Type*} (d B : ℕ) (ξ : Fin d → ℝ)
    (F : I → Finset ℝ) (hF : ∀ i, ∀ v ∈ F i, v = 0 ∨ v34HeightValue d B ξ v)
    (r ε M : ℝ) (l : ℕ) (n : ℤ) (hr : 0 < r) :
    v35TailMax (v36SupValues d B ξ F) r l ε n ≤ M ↔
      0 ≤ M ∧ ∀ i, v35Scale r l n*v36SupMagnitude (F i) ≤ ε →
        v35Scale r l n*v36SupMagnitude (F i) ≤ M := by
  have hs : 0 < v35Scale r l n := by unfold v35Scale; positivity
  constructor
  · intro h
    have hM := (v35_tail_nonneg (v36SupValues d B ξ F) r l ε n).trans h
    refine ⟨hM, ?_⟩
    intro i hi
    by_cases hp : 0 < v36SupMagnitude (F i)
    · have hm := (v36_mem_sup_values d B ξ F hF _).mpr ⟨hp,i,rfl⟩
      exact (v35_tail_dominates _ r l ε n _ hm hi).trans h
    · have hz : v36SupMagnitude (F i) = 0 := le_antisymm (le_of_not_gt hp) (v36_sup_nonneg _)
      simpa [hz] using hM
  · rintro ⟨hM,h⟩
    by_cases hp : 0 < v35TailMax (v36SupValues d B ξ F) r l ε n
    · obtain ⟨v,hv,he,hval⟩ := v35_tail_witness _ r l ε n hp
      obtain ⟨_,i,hi⟩ := (v36_mem_sup_values d B ξ F hF v).mp hv
      rw [hval, ← hi]
      apply h i
      rwa [hi]
    · exact (le_of_not_gt hp).trans hM

/-- Full finiteness in the original family-index formulation. -/
theorem v36_sup_qualifying_finite {I : Type*} (d B l : ℕ) (ξ : Fin d → ℝ)
    (F : I → Finset ℝ) (hF : ∀ i, ∀ v ∈ F i, v = 0 ∨ v34HeightValue d B ξ v)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    {n : ℤ | ∃ i, α ≤ v35Scale r l n*v36SupMagnitude (F i) ∧
      v35Scale r l n*v36SupMagnitude (F i) ≤ β}.Finite := by
  classical
  have he : {n : ℤ | ∃ i, α ≤ v35Scale r l n*v36SupMagnitude (F i) ∧
      v35Scale r l n*v36SupMagnitude (F i) ≤ β} =
      (↑(v36Qualifying (v36SupValues d B ξ F) r α β l) : Set ℤ) := by
    ext n
    exact (v36_sup_mem_qualifying d B l ξ F hF r α β hr hα hαβ hl n).symm
  rw [he]
  exact Finset.finite_toSet _

/-- Same exact finiteness statement for Euclidean vector norms. -/
theorem v36_vector_qualifying_finite {I : Type*} [Fintype I] (h l : ℕ) (a : I → Fin h → ℝ)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l) :
    {n : ℤ | ∃ i, α ≤ v35Scale r l n*v35VectorNorm h (a i) ∧
      v35Scale r l n*v35VectorNorm h (a i) ≤ β}.Finite := by
  classical
  have he : {n : ℤ | ∃ i, α ≤ v35Scale r l n*v35VectorNorm h (a i) ∧
      v35Scale r l n*v35VectorNorm h (a i) ≤ β} =
      (↑(v36Qualifying (v35VectorValues h a) r α β l) : Set ℤ) := by
    ext n
    exact (v36_vector_mem_qualifying h l a r α β hr hα hαβ hl n).symm
  rw [he]
  exact Finset.finite_toSet _

end OpenAI086
