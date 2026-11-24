import OpenAI086.PaperHeightSeparatedChain
import OpenAI086.PaperHeightPacketCover
import OpenAI086.PaperRationalCramerBridge

/-! Lemma 3.5, actual bounded rational evaluations, not a finite-grid
approximation of the frequencies. The real vector is arbitrary. The
corrected scalar logarithmic cover and scale count have explicit budgets.
Source candidates, awaiting kernel verification. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

def v34Eval (d : ℕ) (ξ : Fin d → ℝ) (p : Fin d → ℤ) (q : Fin d → ℕ) : ℝ :=
  |∑ j, ((p j : ℝ)/(q j : ℝ))*ξ j|

/-- Precisely the positive magnitudes of rational evaluations at height B.
Using unreduced fractions gives exactly the same set as reduced fractions. -/
def v34HeightValue (d B : ℕ) (ξ : Fin d → ℝ) (v : ℝ) : Prop :=
  0 < v ∧ ∃ (p : Fin d → ℤ) (q : Fin d → ℕ),
    (∀ j, |(p j : ℝ)| ≤ B) ∧ (∀ j, 0 < q j ∧ q j ≤ B) ∧
    v = v34Eval d ξ p q

/-- Finite enumeration of all allowed rational coefficient vectors.
This does not discretize ξ. -/
abbrev V34Code (d B : ℕ) := Fin d → Fin (2*B+1) × Fin (B+1)

def v34Num {d B : ℕ} (a : V34Code d B) (j : Fin d) : ℤ :=
  ((a j).1.val : ℤ) - (B : ℤ)

def v34Den {d B : ℕ} (a : V34Code d B) (j : Fin d) : ℕ := (a j).2.val

def v34Values (d B : ℕ) (ξ : Fin d → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun a : V34Code d B =>
    (∀ j, 0 < v34Den a j) ∧ 0 < v34Eval d ξ (v34Num a) (v34Den a))).image
    (fun a => v34Eval d ξ (v34Num a) (v34Den a))

/-- Exact equivalence between membership in the enumeration and the
paper's rational-height predicate. -/
theorem v34_mem_values (d B : ℕ) (ξ : Fin d → ℝ) (v : ℝ) :
    v ∈ v34Values d B ξ ↔ v34HeightValue d B ξ v := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha, hv⟩ := Finset.mem_image.mp h
    have hc := (Finset.mem_filter.mp ha).2
    refine ⟨by simpa only [hv] using hc.2, v34Num a, v34Den a, ?_, ?_, hv.symm⟩
    · intro j
      have hj := (a j).1.isLt
      have hbound : |v34Num a j| ≤ (B : ℤ) := by
        unfold v34Num
        rw [abs_le]
        constructor <;> omega
      exact_mod_cast hbound
    · intro j
      exact ⟨hc.1 j, by unfold v34Den; have h := (a j).2.isLt; omega⟩
  · rintro ⟨hv, p, q, hp, hq, he⟩
    have hp' (j : Fin d) : |p j| ≤ (B : ℤ) := by exact_mod_cast hp j
    let a : V34Code d B := fun j =>
      (⟨(p j + (B : ℤ)).toNat, by
          have hh := abs_le.mp (hp' j)
          have ht := Int.toNat_of_nonneg (show 0 ≤ p j + (B : ℤ) by omega)
          omega⟩,
       ⟨q j, by have hh := (hq j).2; omega⟩)
    have hn : v34Num a = p := by
      funext j
      have hh := abs_le.mp (hp' j)
      have ht := Int.toNat_of_nonneg (show 0 ≤ p j + (B : ℤ) by omega)
      change ((p j + (B : ℤ)).toNat : ℤ) - (B : ℤ) = p j
      rw [ht]; ring
    have hd : v34Den a = q := by rfl
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [hn, hd]
      exact ⟨fun j => (hq j).1, by simpa only [he] using hv⟩
    · rw [hn, hd]
      exact he.symm

/-- Explicit separation threshold from V32's bounded integer relation. -/
def v34Ratio (d B : ℕ) : ℝ :=
  1 + (d : ℝ)*(((2*(d+1)*B^d+1)^d : ℕ) : ℝ)*(B^d : ℕ)

def v34Width (d B : ℕ) : ℝ := Real.log (v34Ratio d B) / Real.log 2

theorem v34_ratio_ge_one (d B : ℕ) : 1 ≤ v34Ratio d B := by
  unfold v34Ratio
  have h : 0 ≤ (d : ℝ)*(((2*(d+1)*B^d+1)^d : ℕ) : ℝ)*(B^d : ℕ) := by positivity
  linarith

theorem v34_width_nonneg (d B : ℕ) : 0 ≤ v34Width d B := by
  unfold v34Width
  exact div_nonneg (Real.log_nonneg (v34_ratio_ge_one d B)) (Real.log_pos (by norm_num)).le

/-- A chain of d+1 actual bounded-height rational evaluations is impossible
at the separation threshold. Denominator clearing is derived here. -/
theorem v34_no_height_chain (d B : ℕ) (ξ : Fin d → ℝ)
    (u : Fin (d+1) → ℝ)
    (hu : ∀ i, v34HeightValue d B ξ (u i))
    (hgap : ∀ i j, i < j → v34Ratio d B * u i < u j) : False := by
  classical
  choose p q hp hq he using fun i => (hu i).2
  choose Q hQpos hQle a ha using fun i : Fin (d+1) =>
    v21_clear_vector_denominators (p i) (q i) B
      (fun j => (hq i j).1) (fun j => (hq i j).2) (hp i)
  let w : Fin (d+1) → ℝ := fun i => ∑ j, ((p i j : ℝ)/(q i j : ℝ))*ξ j
  have hw (i : Fin (d+1)) : u i = |w i| := he i
  apply v32_no_long_cleared_chain d (B^d) (B^d) a (fun i => (Q i : ℤ)) ξ w
  · intro i j
    have h := (ha i j).2
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  · intro i
    have hh := hQle i
    rw [Fintype.card_fin] at hh
    exact ⟨by exact_mod_cast hQpos i, by exact_mod_cast hh⟩
  · intro i
    push_cast
    dsimp [w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, (ha i j).1]
  · intro i
    rw [← hw i]
    exact (hu i).1
  · intro i j hij
    rw [← hw i, ← hw j]
    have h := hgap i j hij
    unfold v34Ratio at h
    have hpos := (hu i).1
    nlinarith only [h, hpos]

def v34LogValues (d B : ℕ) (ξ : Fin d → ℝ) : Finset ℝ := by
  classical
  exact (v34Values d B ξ).image (fun v => Real.log v / Real.log 2)

/-- The dimension bound for separated logarithmic centers, with no
additional packing hypothesis. Sort any d+1 centers and lift them to the
actual rational evaluations. -/
theorem v34_log_packing (d B : ℕ) (ξ : Fin d → ℝ) (P : Finset ℝ)
    (hP : P ⊆ v34LogValues d B ξ)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → v34Width d B < |x-y|) : P.card ≤ d := by
  classical
  by_contra hh
  have hc : d+1 ≤ P.card := by omega
  let z := P.orderEmbOfCardLe hc
  have hz (i : Fin (d+1)) : z i ∈ P := Finset.orderEmbOfCardLe_mem P hc i
  have he (i : Fin (d+1)) : ∃ v ∈ v34Values d B ξ, Real.log v / Real.log 2 = z i :=
    Finset.mem_image.mp (hP (hz i))
  choose u hu hlog using he
  have hval (i : Fin (d+1)) := (v34_mem_values d B ξ (u i)).mp (hu i)
  apply v34_no_height_chain d B ξ u hval
  intro i j hij
  have hlt : z i < z j := z.strictMono hij
  have hs := hsep (z j) (hz j) (z i) (hz i) (ne_of_gt hlt)
  rw [abs_of_pos (sub_pos.mpr hlt), ← hlog i, ← hlog j] at hs
  unfold v34Width at hs
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 0 < v34Ratio d B := lt_of_lt_of_le (by norm_num) (v34_ratio_ge_one d B)
  have hloglt : Real.log (v34Ratio d B) + Real.log (u i) < Real.log (u j) := by
    apply (div_lt_div_iff_of_pos_right h2).mp
    rw [add_div]
    linarith
  rw [← Real.log_mul hratio.ne' (hval i).1.ne'] at hloglt
  exact (Real.log_lt_log_iff (mul_pos hratio (hval i).1) (hval j).1).mp hloglt

/-- Scalar part (1): at most d log intervals of width 2W cover all
nonzero rational evaluations. Symmetric intervals cost a factor two. -/
theorem v34_height_log_cover (d B : ℕ) (ξ : Fin d → ℝ) :
    ∃ P : Finset ℝ, P.card ≤ d ∧
      ∀ v, v34HeightValue d B ξ v →
        ∃ p ∈ P, |Real.log v / Real.log 2 - p| ≤ v34Width d B := by
  obtain ⟨P, hP, hc, hs⟩ := v32_separated_net (v34LogValues d B ξ)
    (v34Width d B) (v34_width_nonneg d B)
  refine ⟨P, v34_log_packing d B ξ P hP hs, ?_⟩
  intro v hv
  exact hc _ (Finset.mem_image.mpr ⟨v, (v34_mem_values d B ξ v).mpr hv, rfl⟩)

/-- Corrected scalar part (2) directly for dyadic radii and positive
integer powers, including both powers in the paper. Finite subsets of
the qualifying integers satisfy a uniform bound; the same proof supplies
a finite covering set for all qualifying integers. -/
theorem v34_height_scale_count (d B ℓ : ℕ) (ξ : Fin d → ℝ)
    (r α β : ℝ) (hr : 0 < r) (hα : 0 < α) (hαβ : α ≤ β) (hℓ : 0 < ℓ)
    (S : Finset ℤ)
    (hS : ∀ n ∈ S, ∃ v, v34HeightValue d B ξ v ∧
      α ≤ (r * (2 : ℝ)^(-n))^ℓ*v ∧ (r * (2 : ℝ)^(-n))^ℓ*v ≤ β) :
    (S.card : ℝ) ≤ (d : ℝ)*((2*v34Width d B +
      (Real.log β - Real.log α)/Real.log 2)/(ℓ : ℝ)+1) := by
  classical
  obtain ⟨P, hp, hc⟩ := v34_height_log_cover d B ξ
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hb : 0 < β := lt_of_lt_of_le hα hαβ
  let A := Real.log α / Real.log 2
  let D := Real.log β / Real.log 2
  let R := Real.log r / Real.log 2
  let W := v34Width d B
  have hW : 0 ≤ W := v34_width_nonneg d B
  have hAD : A ≤ D := div_le_div_of_nonneg_right (Real.log_le_log hα hαβ) h2.le
  let a (p : ℝ) := (p-W+(ℓ : ℝ)*R-D)/(ℓ : ℝ)
  let b (p : ℝ) := (p+W+(ℓ : ℝ)*R-A)/(ℓ : ℝ)
  have hcover : ∀ n ∈ S, ∃ p ∈ P, a p ≤ (n : ℝ) ∧ (n : ℝ) ≤ b p := by
    intro n hn
    obtain ⟨v, hv, hlo, hhi⟩ := hS n hn
    obtain ⟨p, hp', hdist⟩ := hc v hv
    have hpos : 0 < r*(2:ℝ)^(-n) := mul_pos hr (zpow_pos (by norm_num) _)
    have hlog : Real.log ((r*(2:ℝ)^(-n))^ℓ*v) =
        (ℓ : ℝ)*(Real.log r - (n:ℝ)*Real.log 2) + Real.log v := by
      rw [Real.log_mul (pow_ne_zero _ hpos.ne') hv.1.ne', Real.log_pow,
        Real.log_mul hr.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
      push_cast <;> ring
    have h1 := Real.log_le_log hα hlo
    have h2' := Real.log_le_log (mul_pos (pow_pos hpos _) hv.1) hhi
    rw [hlog] at h1 h2'
    rw [abs_le] at hdist
    refine ⟨p, hp', ?_, ?_⟩
    · dsimp [a, R, D, W]
      apply (div_le_iff₀ hl).mpr
      have hh := div_le_div_of_nonneg_right h2' h2.le
      have hx : (ℓ:ℝ)*(Real.log r - (n:ℝ)*Real.log 2)/Real.log 2 =
          (ℓ:ℝ)*(Real.log r/Real.log 2 - (n:ℝ)) := by field_simp [h2.ne'] <;> ring
      rw [add_div, hx] at hh
      linarith [hdist.1]
    · dsimp [b, R, A, W]
      apply (le_div_iff₀ hl).mpr
      have hh := div_le_div_of_nonneg_right h1 h2.le
      have hx : (ℓ:ℝ)*(Real.log r - (n:ℝ)*Real.log 2)/Real.log 2 =
          (ℓ:ℝ)*(Real.log r/Real.log 2 - (n:ℝ)) := by field_simp [h2.ne'] <;> ring
      rw [add_div, hx] at hh
      linarith [hdist.2]
  have hwidth : ∀ p : ℝ, b p - a p = (2*W+(D-A))/(ℓ : ℝ) := by
    intro p
    dsimp [a,b]
    ring
  have hnon : 0 ≤ (2*W+(D-A))/(ℓ : ℝ) := div_nonneg (by linarith) hl.le
  have hh := v31_corrected_packet_count P a b ((2*W+(D-A))/(ℓ : ℝ)) 0 S
    hnon (by norm_num) (fun p _ => by linarith [hwidth p])
    (fun p _ => by rw [hwidth]; simp) hcover
  have hp' : (P.card : ℝ) ≤ d := by exact_mod_cast hp
  calc
    _ ≤ (P.card : ℝ)*((2*W+(D-A))/(ℓ : ℝ)+1) := by simpa using hh
    _ ≤ (d : ℝ)*((2*W+(D-A))/(ℓ : ℝ)+1) := by
      exact mul_le_mul_of_nonneg_right hp' (by linarith)
    _ = _ := by dsimp [W,D,A]; ring

/-- The set of occupied dyadic magnitude bins, using floor(log₂ v). -/
def v34HeightBins (d B : ℕ) (ξ : Fin d → ℝ) : Finset ℤ := by
  classical
  exact (v34LogValues d B ξ).image Int.floor

/-- The finite set of actual occupied bins has the asserted polynomial-log
budget once the explicit width is bounded. No restriction on ξ is needed. -/
theorem v34_height_bin_count (d B : ℕ) (ξ : Fin d → ℝ) :
    ((v34HeightBins d B ξ).card : ℝ) ≤ (d : ℝ)*(2*v34Width d B+2) := by
  classical
  obtain ⟨P, hp, hc⟩ := v34_height_log_cover d B ξ
  let W := v34Width d B
  have hW : 0 ≤ W := v34_width_nonneg d B
  have hcover : ∀ n ∈ v34HeightBins d B ξ,
      ∃ p ∈ P, p-W-1 ≤ (n:ℝ) ∧ (n:ℝ) ≤ p+W := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp', hdist⟩ := hc v ((v34_mem_values d B ξ v).mp hv)
    rw [abs_le] at hdist
    have hf := Int.floor_le (Real.log v / Real.log 2)
    have hg := Int.lt_floor_add_one (Real.log v / Real.log 2)
    refine ⟨p, hp', ?_, ?_⟩ <;> dsimp [W] <;> linarith
  have h := v31_corrected_packet_count P (fun p => p-W-1) (fun p => p+W)
    (2*W+1) 0 (v34HeightBins d B ξ) (by linarith) (by norm_num)
    (by intro p hp; linarith) (by intro p hp; linarith) hcover
  have hp' : (P.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ (P.card : ℝ)*(2*W+2) := by convert h using 1 <;> ring
    _ ≤ (d : ℝ)*(2*W+2) := mul_le_mul_of_nonneg_right hp' (by linarith)
    _ = _ := rfl

end OpenAI086
