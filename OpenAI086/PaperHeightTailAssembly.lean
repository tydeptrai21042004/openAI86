import OpenAI086.PaperHeightScalarAssembly
import OpenAI086.DyadicTails

/-! Corrected Lemma 3.5(3). Work with the exact maximum over eligible
values (including zero), all integer scales, and arbitrary real frequencies.
This source is a proof candidate until the pinned Lean kernel accepts it. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators ENNReal

def v35Scale (r : ℝ) (l : ℕ) (n : ℤ) : ℝ := (r * (2 : ℝ)^(-n))^l

def v35Eligible (E : Finset ℝ) (r : ℝ) (l : ℕ) (ε : ℝ) (n : ℤ) : Finset ℝ := by
  classical
  exact insert 0 ((E.filter (fun v => v35Scale r l n * v ≤ ε)).image
    (fun v => v35Scale r l n * v))

def v35TailMax (E : Finset ℝ) (r : ℝ) (l : ℕ) (ε : ℝ) (n : ℤ) : ℝ :=
  (v35Eligible E r l ε n).max' (by classical; simp [v35Eligible])

theorem v35_tail_nonneg (E : Finset ℝ) (r : ℝ) (l : ℕ) (ε : ℝ) (n : ℤ) :
    0 ≤ v35TailMax E r l ε n := by
  classical
  apply Finset.le_max'
  simp [v35Eligible]

theorem v35_tail_witness (E : Finset ℝ) (r : ℝ) (l : ℕ) (ε : ℝ) (n : ℤ)
    (hp : 0 < v35TailMax E r l ε n) :
    ∃ v ∈ E, v35Scale r l n * v ≤ ε ∧
      v35TailMax E r l ε n = v35Scale r l n * v := by
  classical
  have hm := Finset.max'_mem (v35Eligible E r l ε n) (by simp [v35Eligible])
  change v35TailMax E r l ε n ∈ v35Eligible E r l ε n at hm
  simp only [v35Eligible, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hm
  rcases hm with hz | ⟨v, ⟨hv, he⟩, hval⟩
  · exact (hp.ne' hz).elim
  · exact ⟨v, hv, he, hval.symm⟩

theorem v35_tail_dominates (E : Finset ℝ) (r : ℝ) (l : ℕ) (ε : ℝ) (n : ℤ)
    (v : ℝ) (hv : v ∈ E) (he : v35Scale r l n * v ≤ ε) :
    v35Scale r l n * v ≤ v35TailMax E r l ε n := by
  classical
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨v, Finset.mem_filter.mpr ⟨hv, he⟩, rfl⟩)

/-- Integer depths are unrestricted; the relative decay is a natural power. -/
theorem v35_scale_shift (r : ℝ) (l : ℕ) (n0 n : ℤ) (h : n0 ≤ n) :
    v35Scale r l n = v35Scale r l n0 * ((1/2 : ℝ)^((n-n0).toNat))^l := by
  have hk : ((n-n0).toNat : ℤ) = n-n0 := Int.toNat_of_nonneg (by omega)
  have he : -n = -n0 + (-((n-n0).toNat : ℤ)) := by omega
  have hz : (2:ℝ)^(-n) = (2:ℝ)^(-n0) * (1/2:ℝ)^((n-n0).toNat) := by
    calc
      (2:ℝ)^(-n) = (2:ℝ)^(-n0 + (-((n-n0).toNat : ℤ))) := congrArg (fun j : ℤ => (2:ℝ)^j) he
      _ = _ := by rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_neg, zpow_natCast]; simp [one_div, inv_pow]
  unfold v35Scale
  rw [hz, ← mul_assoc, mul_pow]

/-- Sum over arbitrary integer depths in one magnitude packet. Choose the
first nonzero contribution in the actual finite set, not a fixed horizon. -/
theorem v35_one_packet_tail (E : Finset ℝ) (r ε : ℝ) (l : ℕ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2)
    (hpacket : ∀ u ∈ E, ∀ v ∈ E, v ≤ 2*u) (S : Finset ℤ) :
    (∑ n ∈ S, v35TailMax E r l ε n) ≤ 4*ε := by
  classical
  let A := v35TailMax E r l ε
  let F := S.filter (fun n => 0 < A n)
  have hsum : (∑ n ∈ S, A n) = ∑ n ∈ F, A n := by
    rw [show F = S.filter (fun n => 0 < A n) by rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · exact le_antisymm (le_of_not_gt h) (v35_tail_nonneg E r l ε n)
  change (∑ n ∈ S, A n) ≤ _
  rw [hsum]
  by_cases hF : F.Nonempty
  · let n0 := F.min' hF
    have hn0 : n0 ∈ F := Finset.min'_mem F hF
    obtain ⟨u, hu, hue, _⟩ := v35_tail_witness E r l ε n0 (Finset.mem_filter.mp hn0).2
    let k (n : ℤ) := (n-n0).toNat
    have hmin (n : ℤ) (hn : n ∈ F) : n0 ≤ n := Finset.min'_le F n hn
    have hk (n : ℤ) (hn : n ∈ F) : (k n : ℤ) = n-n0 := Int.toNat_of_nonneg (sub_nonneg.mpr (hmin n hn))
    have hinj : Set.InjOn k (↑F : Set ℤ) := by
      intro a ha b hb hab
      have h1 := hk a ha
      have h2 := hk b hb
      have h3 : (k a : ℤ) = (k b : ℤ) := congrArg (fun x : ℕ => (x : ℤ)) hab
      omega
    have hbound (n : ℤ) (hn : n ∈ F) : A n ≤ (2*ε)*((1/2:ℝ)^(k n)) := by
      obtain ⟨v, hv, _, hval⟩ := v35_tail_witness E r l ε n (Finset.mem_filter.mp hn).2
      have hs : 0 ≤ v35Scale r l n0 := by unfold v35Scale; positivity
      have hdec : 0 ≤ (1/2:ℝ)^(k n) := by positivity
      have hdec1 : (1/2:ℝ)^(k n) ≤ 1 := by
        have hh (m : ℕ) : (1/2:ℝ)^m ≤ 1 := by
          induction m with
          | zero => norm_num
          | succ m ih => rw [pow_succ]; linarith
        exact hh (k n)
      have hpow : ((1/2:ℝ)^(k n))^l ≤ (1/2:ℝ)^(k n) := by
        rcases hl with rfl | rfl
        · simp
        · rw [pow_two]; nlinarith
      have hv' : v35Scale r l n0 * v ≤ 2*ε := by
        calc
          _ ≤ v35Scale r l n0 * (2*u) := mul_le_mul_of_nonneg_left (hpacket u hu v hv) hs
          _ = 2*(v35Scale r l n0*u) := by ring
          _ ≤ _ := by linarith
      change v35TailMax E r l ε n ≤ _
      rw [hval, v35_scale_shift r l n0 n (hmin n hn)]
      change v35Scale r l n0 * ((1/2:ℝ)^(k n))^l * v ≤ _
      calc
        _ = (v35Scale r l n0 * v) * ((1/2:ℝ)^(k n))^l := by ring
        _ ≤ (2*ε) * ((1/2:ℝ)^(k n))^l := mul_le_mul_of_nonneg_right hv' (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
    let K := F.image k
    let N := K.sup id + 1
    have hsub : K ⊆ Finset.range N := by
      intro j hj
      have hh : j ≤ K.sup id := Finset.le_sup (f := id) hj
      exact Finset.mem_range.mpr (by dsimp [N]; omega)
    calc
      _ ≤ ∑ n ∈ F, (2*ε)*((1/2:ℝ)^(k n)) := Finset.sum_le_sum hbound
      _ = ∑ j ∈ K, (2*ε)*((1/2:ℝ)^j) := by
        dsimp [K]; rw [Finset.sum_image hinj]
      _ ≤ ∑ j ∈ Finset.range N, (2*ε)*((1/2:ℝ)^j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro j _ _; positivity)
      _ ≤ 4*ε := by
        have hh := dyadic_tail_with_amplitude (2*ε) (by positivity) N
        linarith
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [he, hε]

/-- The floor of the logarithm identifies the occupied dyadic bins. -/
def v35Bin (v : ℝ) : ℤ := Int.floor (Real.log v / Real.log 2)

theorem v35_same_bin_ratio (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h : v35Bin u = v35Bin v) : v ≤ 2*u := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := Int.floor_le (Real.log u / Real.log 2)
  have h3 := Int.lt_floor_add_one (Real.log v / Real.log 2)
  change v35Bin u = v35Bin v at h
  change (v35Bin u : ℝ) ≤ _ at h1
  change _ < (v35Bin v : ℝ) + 1 at h3
  rw [← h] at h3
  have hlt : Real.log v / Real.log 2 < Real.log u / Real.log 2 + 1 := by linarith
  have hlt' : Real.log v < Real.log (2*u) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hu.ne']
    apply (div_lt_div_iff_of_pos_right h2).mp
    rw [add_div, div_self h2.ne']
    linarith
  exact ((Real.log_lt_log_iff hv (mul_pos (by norm_num) hu)).mp hlt').le

/-- Full finite-subsum form of the scalar tail bound, with the exact
number of occupied bins. No input bound on the frequency magnitudes. -/
theorem v35_tail_by_bins (E : Finset ℝ) (r ε : ℝ) (l : ℕ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2)
    (hE : ∀ v ∈ E, 0 < v) (S : Finset ℤ) :
    (∑ n ∈ S, v35TailMax E r l ε n) ≤ ((E.image v35Bin).card : ℝ)*(4*ε) := by
  classical
  let J := E.image v35Bin
  let E' (b : ℤ) := E.filter (fun v => v35Bin v = b)
  have hpt (b : ℤ) : ∀ u ∈ E' b, ∀ v ∈ E' b, v ≤ 2*u := by
    intro u hu v hv
    obtain ⟨hu', hub⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv', hvb⟩ := Finset.mem_filter.mp hv
    exact v35_same_bin_ratio u v (hE u hu') (hE v hv') (hub.trans hvb.symm)
  have hpoint (n : ℤ) : v35TailMax E r l ε n ≤ ∑ b ∈ J, v35TailMax (E' b) r l ε n := by
    by_cases hp : 0 < v35TailMax E r l ε n
    · obtain ⟨v, hv, hle, he⟩ := v35_tail_witness E r l ε n hp
      have hj : v35Bin v ∈ J := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hv' : v ∈ E' (v35Bin v) := Finset.mem_filter.mpr ⟨hv, rfl⟩
      rw [he]
      exact (v35_tail_dominates (E' (v35Bin v)) r l ε n v hv' hle).trans
        (Finset.single_le_sum (fun b _ => v35_tail_nonneg (E' b) r l ε n) hj)
    · exact (le_of_not_gt hp).trans (Finset.sum_nonneg (fun b _ => v35_tail_nonneg (E' b) r l ε n))
  calc
    _ ≤ ∑ n ∈ S, ∑ b ∈ J, v35TailMax (E' b) r l ε n := Finset.sum_le_sum (fun n _ => hpoint n)
    _ = ∑ b ∈ J, ∑ n ∈ S, v35TailMax (E' b) r l ε n := Finset.sum_comm
    _ ≤ ∑ b ∈ J, 4*ε := Finset.sum_le_sum (fun b _ => v35_one_packet_tail (E' b) r ε l hr hε hl (hpt b) S)
    _ = _ := by simp [J]

/-- The nonnegative infinite sum over all integer scales. In contrast to
using a real tsum without proving summability, ENNReal records divergence
as infinity, so this finite upper bound is a substantive assertion. -/
theorem v35_tail_infinite (E : Finset ℝ) (r ε : ℝ) (l : ℕ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2)
    (hE : ∀ v ∈ E, 0 < v) :
    (∑' n : ℤ, ENNReal.ofReal (v35TailMax E r l ε n)) ≤
      ENNReal.ofReal (((E.image v35Bin).card : ℝ)*(4*ε)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => v35_tail_nonneg E r l ε n)]
  exact ENNReal.ofReal_le_ofReal (v35_tail_by_bins E r ε l hr hε hl hE S)

/-- The actual bounded rational-height scalar tail in Lemma 3.5(3). -/
theorem v35_height_tail (d B : ℕ) (ξ : Fin d → ℝ) (r ε : ℝ) (l : ℕ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2) :
    (∑' n : ℤ, ENNReal.ofReal (v35TailMax (v34Values d B ξ) r l ε n)) ≤
      ENNReal.ofReal ((d:ℝ)*(2*v34Width d B+2)*(4*ε)) := by
  classical
  have hE : ∀ v ∈ v34Values d B ξ, 0 < v := fun v hv => ((v34_mem_values d B ξ v).mp hv).1
  have hb : (v34Values d B ξ).image v35Bin = v34HeightBins d B ξ := by
    simp [v34HeightBins, v34LogValues, v35Bin, Finset.image_image, Function.comp_def]
  apply (v35_tail_infinite (v34Values d B ξ) r ε l hr hε hl hE).trans
  apply ENNReal.ofReal_le_ofReal
  rw [hb]
  exact mul_le_mul_of_nonneg_right (v34_height_bin_count d B ξ) (by positivity)

/-- Transfer a genuine finite ENNReal sum to a summable real series. -/
theorem v35_real_series_of_bound (f : ℤ → ℝ) (K : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hK : 0 ≤ K)
    (h : (∑' n : ℤ, ENNReal.ofReal (f n)) ≤ ENNReal.ofReal K) :
    Summable f ∧ (∑' n : ℤ, f n) ≤ K := by
  have hfinite : (∑' n : ℤ, ENNReal.ofReal (f n)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  have hs : Summable f := by
    have heq : (fun n : ℤ => (ENNReal.ofReal (f n)).toReal) = f := by
      funext n; exact ENNReal.toReal_ofReal (hf n)
    rw [← heq]
    exact ENNReal.summable_toReal hfinite
  refine ⟨hs, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf), ENNReal.toReal_ofReal hK] at hh
  exact hh

/-- Ordinary real-series version of the actual scalar tail, including convergence. -/
theorem v35_height_real_tail (d B : ℕ) (ξ : Fin d → ℝ) (r ε : ℝ) (l : ℕ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hl : l = 1 ∨ l = 2) :
    Summable (v35TailMax (v34Values d B ξ) r l ε) ∧
    (∑' n : ℤ, v35TailMax (v34Values d B ξ) r l ε n) ≤
      (d:ℝ)*(2*v34Width d B+2)*(4*ε) := by
  apply v35_real_series_of_bound
  · intro n; exact v35_tail_nonneg _ _ _ _ _
  · have hw := v34_width_nonneg d B; positivity
  · exact v35_height_tail d B ξ r ε l hr hε hl

end OpenAI086
