import OpenAI086.PaperHeightTailAssembly

/-! Vector extension of the corrected height-bin lemma. The coordinates
are actual rational evaluations; they may vary with the vector and no
size bound on the unrestricted real frequency vector is imposed. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators ENNReal

/-- Explicit polynomial logarithmic bound for the scalar packet radius. -/
theorem v35_height_width_bound (d B : ℕ) (hd : 1 ≤ d) (hB : 2 ≤ B) :
    v34Width d B ≤ 4*((d:ℝ)+1)^2*(Real.log (2*(B:ℝ))/Real.log 2) := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hB' : (2:ℝ) ≤ B := by exact_mod_cast hB
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBpos : (0:ℝ) < B := by linarith
  have hdpos : (0:ℝ) < d := by linarith
  have hpow (n : ℕ) : (n:ℝ)+1 ≤ (2:ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      push_cast
      rw [pow_succ]
      have hn : (0:ℝ) ≤ n := by positivity
      linarith
  let L := Real.log (2*(B:ℝ))
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by dsimp [L]; linarith)
  have hLB : Real.log (B:ℝ) ≤ L := Real.log_le_log hBpos (by dsimp [L]; linarith)
  have hL : 0 ≤ L := h2.le.trans hL2
  have hlogD : Real.log ((d:ℝ)+1) ≤ (d:ℝ)*L := by
    have hh := Real.log_le_log (show 0 < (d:ℝ)+1 by positivity) (hpow d)
    rw [Real.log_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hL2 (by positivity))
  have hlogd : Real.log (d:ℝ) ≤ (d:ℝ)*L :=
    (Real.log_le_log hdpos (by linarith)).trans hlogD
  let x : ℝ := 2*((d:ℝ)+1)*(B:ℝ)^d
  have hx : 1 ≤ x := by
    have hbpow : 1 ≤ (B:ℝ)^d := one_le_pow₀ (by linarith) _
    dsimp [x]
    nlinarith
  have hlogx : Real.log (x+1) ≤ (2*(d:ℝ)+2)*L := by
    calc
      _ ≤ Real.log (2*x) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + (Real.log 2 + Real.log ((d:ℝ)+1)) + (d:ℝ)*Real.log (B:ℝ) := by
        dsimp [x]
        rw [Real.log_mul (by norm_num) (by positivity : 2*((d:ℝ)+1)*(B:ℝ)^d ≠ 0),
          Real.log_mul (by positivity : 2*((d:ℝ)+1) ≠ 0) (pow_ne_zero _ hBpos.ne'),
          Real.log_mul (by norm_num) (by positivity : (d:ℝ)+1 ≠ 0), Real.log_pow]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hLB (show 0 ≤ (d:ℝ) by positivity)
        linarith
  let y : ℝ := (d:ℝ)*(x+1)^d*(B:ℝ)^d
  have hy : 1 ≤ y := by
    have hp1 : 1 ≤ (x+1)^d := one_le_pow₀ (by linarith) _
    have hp2 : 1 ≤ (B:ℝ)^d := one_le_pow₀ (by linarith) _
    dsimp [y]
    calc
      1 = 1*1*1 := by norm_num
      _ ≤ (d:ℝ)*(x+1)^d*(B:ℝ)^d := by gcongr
  have hratio : v34Ratio d B = 1+y := by
    unfold v34Ratio
    dsimp [y,x]
    push_cast
    ring
  unfold v34Width
  rw [hratio]
  apply (div_le_iff₀ h2).mpr
  calc
    Real.log (1+y) ≤ Real.log (2*y) := Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + (Real.log (d:ℝ)+(d:ℝ)*Real.log (x+1)) + (d:ℝ)*Real.log (B:ℝ) := by
      dsimp [y]
      rw [Real.log_mul (by norm_num) (by positivity : (d:ℝ)*(x+1)^d*(B:ℝ)^d ≠ 0),
        Real.log_mul (by positivity : (d:ℝ)*(x+1)^d ≠ 0) (pow_ne_zero _ hBpos.ne'),
        Real.log_mul hdpos.ne' (pow_ne_zero _ (by linarith : x+1 ≠ 0)), Real.log_pow, Real.log_pow]
      ring
    _ ≤ (2*(d:ℝ)^2+4*(d:ℝ)+1)*L := by
      have hh := mul_le_mul_of_nonneg_left hlogx (show 0 ≤ (d:ℝ) by positivity)
      have hh' := mul_le_mul_of_nonneg_left hLB (show 0 ≤ (d:ℝ) by positivity)
      linarith
    _ ≤ 4*((d:ℝ)+1)^2*(Real.log (2*(B:ℝ))/Real.log 2)*Real.log 2 := by
      have hh : 2*(d:ℝ)^2+4*(d:ℝ)+1 ≤ 4*((d:ℝ)+1)^2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hh hL
      dsimp [L] at hmul
      calc
        _ ≤ _ := hmul
        _ = _ := by field_simp [h2.ne']

/-- Magnitudes of the coordinates of an evaluation vector. Zero
coordinates are allowed and do not contribute to the positive value set. -/
def v35VectorNorm (h : ℕ) (a : Fin h → ℝ) : ℝ := Real.sqrt (∑ j, (a j)^2)

theorem v35_vector_comparison (d B h : ℕ) (ξ : Fin d → ℝ) (a : Fin h → ℝ)
    (ha : ∀ j, a j = 0 ∨ v34HeightValue d B ξ |a j|)
    (hpos : 0 < v35VectorNorm h a) :
    ∃ u, v34HeightValue d B ξ u ∧ u ≤ v35VectorNorm h a ∧
      v35VectorNorm h a ≤ Real.sqrt (h:ℝ)*u := by
  classical
  let F : Finset ℝ := insert 0 (Finset.univ.image (fun j : Fin h => |a j|))
  have hF : F.Nonempty := by simp [F]
  let u := F.max' hF
  have hu : u ∈ F := Finset.max'_mem F hF
  have hu0 : 0 ≤ u := Finset.le_max' F 0 (by simp [F])
  have hmax (j : Fin h) : |a j| ≤ u := Finset.le_max' F _ (by simp [F])
  have hs : (∑ j, (a j)^2) ≤ (h:ℝ)*u^2 := by
    calc
      _ = ∑ j, |a j|^2 := by simp
      _ ≤ ∑ _j : Fin h, u^2 := Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hmax j) 2)
      _ = _ := by simp
  have hnorm : (v35VectorNorm h a)^2 = ∑ j, (a j)^2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hupper : v35VectorNorm h a ≤ Real.sqrt (h:ℝ)*u := by
    have hsqrt : (Real.sqrt (h:ℝ))^2 = (h:ℝ) := Real.sq_sqrt (by positivity)
    have hsq : (v35VectorNorm h a)^2 ≤ (Real.sqrt (h:ℝ)*u)^2 := by
      rw [hnorm, mul_pow, hsqrt]; exact hs
    have hr : 0 ≤ Real.sqrt (h:ℝ)*u := mul_nonneg (Real.sqrt_nonneg _) hu0
    nlinarith
  have hup : 0 < u := by
    by_contra hn
    have hz : u = 0 := le_antisymm (le_of_not_gt hn) hu0
    rw [hz, mul_zero] at hupper
    linarith
  simp only [F, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu
  rcases hu with hzero | ⟨j, hj⟩
  · exact (hup.ne' hzero).elim
  · have hcoord : v34HeightValue d B ξ u := by
      rcases ha j with hz | hv
      · rw [hz, abs_zero] at hj
        exact (hup.ne' hj.symm).elim
      · simpa only [hj] using hv
    have hlow : u ≤ v35VectorNorm h a := by
      have hh : (a j)^2 ≤ ∑ k, (a k)^2 := Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ j)
      have hsq : u^2 ≤ (v35VectorNorm h a)^2 := by rw [← hj, sq_abs, hnorm]; exact hh
      nlinarith
    exact ⟨u, hcoord, hlow, hupper⟩

/-- Arbitrary finite families of positive Euclidean evaluation norms.
Enlarge each scalar logarithmic packet by half log₂(h). -/
theorem v35_vector_log_cover {I : Type*} [Fintype I] (d B h : ℕ)
    (ξ : Fin d → ℝ) (a : I → Fin h → ℝ) (hh : 1 ≤ h)
    (ha : ∀ i j, a i j = 0 ∨ v34HeightValue d B ξ |a i j|) :
    ∃ P : Finset ℝ, P.card ≤ d ∧
      ∀ i, 0 < v35VectorNorm h (a i) → ∃ p ∈ P,
        p-v34Width d B ≤ Real.log (v35VectorNorm h (a i))/Real.log 2 ∧
        Real.log (v35VectorNorm h (a i))/Real.log 2 ≤
          p+v34Width d B+Real.log (h:ℝ)/(2*Real.log 2) := by
  obtain ⟨P, hp, hc⟩ := v34_height_log_cover d B ξ
  refine ⟨P, hp, ?_⟩
  intro i hi
  obtain ⟨u, hu, hlo, hhi⟩ := v35_vector_comparison d B h ξ (a i) (ha i) hi
  obtain ⟨p, hp', hpdist⟩ := hc u hu
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh' : 0 < (h:ℝ) := by exact_mod_cast (show 0 < h by omega)
  have hroot : 0 < Real.sqrt (h:ℝ) := Real.sqrt_pos.2 hh'
  have hlog1 := div_le_div_of_nonneg_right (Real.log_le_log hu.1 hlo) h2.le
  have hlog2 := div_le_div_of_nonneg_right (Real.log_le_log hi hhi) h2.le
  rw [Real.log_mul hroot.ne' hu.1.ne', Real.log_sqrt hh'.le, add_div] at hlog2
  rw [abs_le] at hpdist
  refine ⟨p, hp', ?_, ?_⟩
  · linarith [hpdist.1]
  · have he : Real.log (h:ℝ)/2/Real.log 2 = Real.log (h:ℝ)/(2*Real.log 2) := by ring
    rw [he] at hlog2
    linarith [hpdist.2]

/-- All occupied vector norm bins, not only the scalar coordinate bins. -/
def v35VectorValues {I : Type*} [Fintype I] (h : ℕ) (a : I → Fin h → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.image (fun i => v35VectorNorm h (a i))).filter (fun v => 0 < v)

theorem v35_vector_bin_count {I : Type*} [Fintype I] (d B h : ℕ)
    (ξ : Fin d → ℝ) (a : I → Fin h → ℝ) (hh : 1 ≤ h)
    (ha : ∀ i j, a i j = 0 ∨ v34HeightValue d B ξ |a i j|) :
    (((v35VectorValues h a).image v35Bin).card : ℝ) ≤
      (d:ℝ)*(2*v34Width d B+Real.log (h:ℝ)/(2*Real.log 2)+2) := by
  classical
  obtain ⟨P, hp, hc⟩ := v35_vector_log_cover d B h ξ a hh ha
  let W := v34Width d B
  let U := Real.log (h:ℝ)/(2*Real.log 2)
  have hW : 0 ≤ W := v34_width_nonneg d B
  have hU : 0 ≤ U := div_nonneg (Real.log_nonneg (by exact_mod_cast hh)) (by positivity)
  have hcover : ∀ n ∈ (v35VectorValues h a).image v35Bin,
      ∃ p ∈ P, p-W-1 ≤ (n:ℝ) ∧ (n:ℝ) ≤ p+W+U := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hv', hvpos⟩ := Finset.mem_filter.mp hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv'
    obtain ⟨p, hp', hlow, hhigh⟩ := hc i hvpos
    have hf := Int.floor_le (Real.log (v35VectorNorm h (a i))/Real.log 2)
    have hg := Int.lt_floor_add_one (Real.log (v35VectorNorm h (a i))/Real.log 2)
    refine ⟨p, hp', ?_, ?_⟩ <;> unfold v35Bin <;> dsimp [W,U] <;> linarith
  have h := v31_corrected_packet_count P (fun p => p-W-1) (fun p => p+W+U)
    (2*W+1) U ((v35VectorValues h a).image v35Bin) (by linarith) hU
    (by intro p hp; linarith) (by intro p hp; linarith) hcover
  have hp' : (P.card:ℝ) ≤ d := by exact_mod_cast hp
  calc
    _ ≤ (P.card:ℝ)*(2*W+U+2) := by convert h using 1 <;> ring
    _ ≤ (d:ℝ)*(2*W+U+2) := mul_le_mul_of_nonneg_right hp' (by linarith)
    _ = _ := rfl

theorem v35_vector_tail {I : Type*} [Fintype I] (d B h : ℕ)
    (ξ : Fin d → ℝ) (a : I → Fin h → ℝ) (hh : 1 ≤ h)
    (ha : ∀ i j, a i j = 0 ∨ v34HeightValue d B ξ |a i j|)
    (r ε : ℝ) (l : ℕ) (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2) :
    (∑' n : ℤ, ENNReal.ofReal (v35TailMax (v35VectorValues h a) r l ε n)) ≤
      ENNReal.ofReal ((d:ℝ)*(2*v34Width d B+Real.log (h:ℝ)/(2*Real.log 2)+2)*(4*ε)) := by
  classical
  apply (v35_tail_infinite (v35VectorValues h a) r ε l hr hε hl
    (fun v hv => (Finset.mem_filter.mp hv).2)).trans
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (v35_vector_bin_count d B h ξ a hh ha) (by positivity))

/-- Real summability and total mass for Euclidean vector norms. -/
theorem v35_vector_real_tail {I : Type*} [Fintype I] (d B h : ℕ)
    (ξ : Fin d → ℝ) (a : I → Fin h → ℝ) (hh : 1 ≤ h)
    (ha : ∀ i j, a i j = 0 ∨ v34HeightValue d B ξ |a i j|)
    (r ε : ℝ) (l : ℕ) (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2) :
    Summable (v35TailMax (v35VectorValues h a) r l ε) ∧
    (∑' n : ℤ, v35TailMax (v35VectorValues h a) r l ε n) ≤
      (d:ℝ)*(2*v34Width d B+Real.log (h:ℝ)/(2*Real.log 2)+2)*(4*ε) := by
  apply v35_real_series_of_bound
  · intro n; exact v35_tail_nonneg _ _ _ _ _
  · have hw := v34_width_nonneg d B
    have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
    have hu := Real.log_nonneg hh'
    positivity
  · exact v35_vector_tail d B h ξ a hh ha r ε l hr hε hl

/-- Corrected scale count for the vector norms. This is a finite-subset
bound, as in the scalar candidate. All actual qualifying scales are
contained in the finitely many integer windows in the proof. -/
theorem v35_vector_scale_count {I : Type*} [Fintype I] (d B h l : ℕ)
    (ξ : Fin d → ℝ) (a : I → Fin h → ℝ) (hh : 1 ≤ h)
    (ha : ∀ i j, a i j = 0 ∨ v34HeightValue d B ξ |a i j|)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hl : 0 < l)
    (S : Finset ℤ)
    (hS : ∀ n ∈ S, ∃ i, α ≤ v35Scale r l n*v35VectorNorm h (a i) ∧
      v35Scale r l n*v35VectorNorm h (a i) ≤ β) :
    (S.card:ℝ) ≤ (d:ℝ)*((2*v34Width d B+Real.log (h:ℝ)/(2*Real.log 2)+
      (Real.log β-Real.log α)/Real.log 2)/(l:ℝ)+1) := by
  classical
  obtain ⟨P, hp, hc⟩ := v35_vector_log_cover d B h ξ a hh ha
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl' : 0 < (l:ℝ) := by exact_mod_cast hl
  let W := v34Width d B
  let U := Real.log (h:ℝ)/(2*Real.log 2)
  let A := Real.log α / Real.log 2
  let D := Real.log β / Real.log 2
  let R := Real.log r / Real.log 2
  let lo (p:ℝ) := (p-W+(l:ℝ)*R-D)/(l:ℝ)
  let hi (p:ℝ) := (p+W+U+(l:ℝ)*R-A)/(l:ℝ)
  have hw : 0 ≤ W := v34_width_nonneg d B
  have hu : 0 ≤ U := div_nonneg (Real.log_nonneg (by exact_mod_cast hh)) (by positivity)
  have hAD : A ≤ D := div_le_div_of_nonneg_right (Real.log_le_log hα hαβ) h2.le
  have hcover : ∀ n ∈ S, ∃ p ∈ P, lo p ≤ (n:ℝ) ∧ (n:ℝ) ≤ hi p := by
    intro n hn
    obtain ⟨i, hlow, hhigh⟩ := hS n hn
    let v := v35VectorNorm h (a i)
    have hscale : 0 < v35Scale r l n := by unfold v35Scale; positivity
    have hv : 0 < v := pos_of_mul_pos_left (lt_of_lt_of_le hα hlow) hscale.le
    obtain ⟨p, hp', hplo, hphi⟩ := hc i hv
    have hlog : Real.log (v35Scale r l n*v) =
        (l:ℝ)*(Real.log r-(n:ℝ)*Real.log 2)+Real.log v := by
      unfold v35Scale
      rw [Real.log_mul (pow_ne_zero _ (by positivity)) hv.ne', Real.log_pow,
        Real.log_mul hr.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
      push_cast <;> ring
    have h1 := div_le_div_of_nonneg_right (Real.log_le_log hα hlow) h2.le
    have h3 := div_le_div_of_nonneg_right (Real.log_le_log (mul_pos hscale hv) hhigh) h2.le
    rw [hlog, add_div] at h1 h3
    have hx : (l:ℝ)*(Real.log r-(n:ℝ)*Real.log 2)/Real.log 2 =
        (l:ℝ)*(R-(n:ℝ)) := by dsimp [R]; field_simp [h2.ne'] <;> ring
    rw [hx] at h1 h3
    refine ⟨p, hp', ?_, ?_⟩
    · apply (div_le_iff₀ hl').mpr
      dsimp [lo, W, D, R] at *
      linarith
    · apply (le_div_iff₀ hl').mpr
      dsimp [hi, W, U, A, R] at *
      linarith
  let Q := (2*W+U+(D-A))/(l:ℝ)
  have hQ : 0 ≤ Q := div_nonneg (by linarith) hl'.le
  have hwidth (p:ℝ) : hi p-lo p = Q := by dsimp [hi,lo,Q]; ring
  have ht := v31_corrected_packet_count P lo hi Q 0 S hQ (by norm_num)
    (fun p _ => by linarith [hwidth p]) (fun p _ => by rw [hwidth]; simp) hcover
  have hcard : (P.card:ℝ) ≤ d := by exact_mod_cast hp
  calc
    _ ≤ (P.card:ℝ)*(Q+1) := by simpa using ht
    _ ≤ (d:ℝ)*(Q+1) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by dsimp [Q,W,U,D,A]; ring

end OpenAI086
