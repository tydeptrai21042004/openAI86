import Mathlib
import OpenAI086.PaperAccuracySummation

/-! Proposition 9.2, p.88: turn the low-density mass estimate (36) into
its powered sum, with an actual finite dyadic partition and a constant
independent of the number of scales. The density estimate is an input
from the still-open Lemma 9.1, not a consequence of this module. -/
namespace OpenAI086

private theorem half_pow_le_one (n : ℕ) : (1/2:ℝ)^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

private theorem half_pow_antitone {m n : ℕ} (h : m ≤ n) :
    (1/2:ℝ)^n ≤ (1/2:ℝ)^m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact mul_le_of_le_one_right (by positivity) (half_pow_le_one k)

/-- A positive real value is above some dyadic threshold. This is
proved by the Archimedean property, not a fixed artificial scale cap. -/
theorem v40_positive_dyadic_cut (x : ℝ) (hx : 0 < x) :
    ∃ n : ℕ, (1/2:ℝ)^n < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1/x)
  have h2 : (n:ℝ)+1 ≤ (2:ℝ)^n := by exact_mod_cast v39_level_multiplicity n
  have hgt : 1/x < (2:ℝ)^n := by linarith
  have hp : 1 < (2:ℝ)^n*x := (div_lt_iff₀ hx).mp hgt
  refine ⟨n, ?_⟩
  rw [div_pow, one_pow]
  exact (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^n)).mpr (by linarith)

/-- A finite set of nonnegative densities has a uniform dyadic cutoff
for its positive members; zero members never need to be put in a bin. -/
theorem v40_finite_density_cut {I : Type*} (s : Finset I) (x : I → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∃ N : ℕ, ∀ i ∈ s, x i = 0 ∨ (1/2:ℝ)^N < x i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨N, hN⟩ := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    by_cases hz : x i = 0
    · refine ⟨N, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Or.inl hz
      · exact hN j hj
    · obtain ⟨n, hn⟩ := v40_positive_dyadic_cut (x i)
          (lt_of_le_of_ne (hx i (Finset.mem_insert_self _ _)) (Ne.symm hz))
      refine ⟨max N n, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Or.inr ((half_pow_antitone (le_max_right N n)).trans_lt hn)
      · rcases hN j hj with h | h
        · exact Or.inl h
        · exact Or.inr ((half_pow_antitone (le_max_left N n)).trans_lt h)

/-- Every positive density above the cutoff belongs to a dyadic band
(q^(j+1), q^j], including values exactly at an upper endpoint. -/
theorem v40_dyadic_band (x : ℝ) (hx : x ≤ 1) (N : ℕ)
    (hcut : (1/2:ℝ)^N < x) :
    ∃ j : ℕ, j < N ∧ (1/2:ℝ)^(j+1) < x ∧ x ≤ (1/2:ℝ)^j := by
  induction N with
  | zero => simp at hcut; linarith
  | succ N ih =>
    by_cases h : (1/2:ℝ)^N < x
    · obtain ⟨j, hj, hlo, hhi⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hlo, hhi⟩
    · exact ⟨N, Nat.lt_succ_self _, hcut, le_of_not_gt h⟩

private theorem half_rpow_nat (a : ℝ) (n : ℕ) :
    ((1/2:ℝ)^n)^a = ((1/2:ℝ)^a)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.mul_rpow (by positivity : 0 ≤ (1/2:ℝ)^n)
      (by norm_num : (0:ℝ) ≤ 1/2), ih, pow_succ]

private theorem geom_sum_mul (r : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, r^j)*(1-r) = 1-r^N := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

/-- The complete powered conversion for finite normalized densities.
The dyadic low-mass estimate is the only density hypothesis. -/
theorem v40_density_to_power {I : Type*} (s : Finset I) (x : I → ℝ)
    (p c K : ℝ) (hp : 0 < p) (hp1 : p < 1) (hc : 1-p < c)
    (hK : 0 ≤ K) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (hmass : ∀ j : ℕ,
      (∑ i ∈ s.filter (fun i => x i ≤ (1/2:ℝ)^j), x i) ≤
        K*((1/2:ℝ)^c)^j) :
    let b := (1/2:ℝ)^(1-p)
    let r := (1/2:ℝ)^c/b
    (∑ i ∈ s, (x i)^p) ≤ K/(b*(1-r)) := by
  classical
  let b := (1/2:ℝ)^(1-p)
  let a := (1/2:ℝ)^c
  let r := a/b
  have hb : 0 < b := by dsimp [b]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by
    dsimp [a,b]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2),
      Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 1/2)]
    apply Real.exp_lt_exp.mpr
    have hlog : Real.log (1/2:ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    first | exact mul_lt_mul_of_neg_left hc hlog | exact mul_lt_mul_of_neg_right hc hlog
  have hr : 0 ≤ r := div_nonneg ha.le hb.le
  have hr1 : r < 1 := (div_lt_iff₀ hb).mpr (by simpa using hab)
  obtain ⟨N, hN⟩ := v40_finite_density_cut s x (fun i hi => (hx i hi).1)
  let band := fun j : ℕ => s.filter (fun i => (1/2:ℝ)^(j+1) < x i ∧ x i ≤ (1/2:ℝ)^j)
  have hband (j : ℕ) : (∑ i ∈ band j, (x i)^p) ≤ (K/b)*r^j := by
    have hpoint (i : I) (hi : i ∈ band j) : (x i)^p ≤ x i / b^(j+1) := by
      have hh := (Finset.mem_filter.mp hi).2.1
      have hpos : 0 < x i := (by positivity : 0 < (1/2:ℝ)^(j+1)).trans hh
      have hl : b^(j+1) ≤ (x i)^(1-p) := by
        dsimp [b]
        rw [← half_rpow_nat]
        exact Real.rpow_le_rpow (by positivity) hh.le (by linarith)
      apply (le_div_iff₀ (pow_pos hb _)).mpr
      calc
        _ ≤ (x i)^p * (x i)^(1-p) := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hpos.le _)
        _ = x i := by
          rw [← Real.rpow_add hpos]
          have h : p+(1-p)=1 := by ring
          rw [h, Real.rpow_one]
    have hmass' : (∑ i ∈ band j, x i) ≤ K*a^j := by
      apply le_trans _ (hmass j)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
          (Finset.mem_filter.mp hi).2.2⟩)
        (fun i hi _ => (hx i (Finset.mem_filter.mp hi).1).1)
    calc
      _ ≤ ∑ i ∈ band j, x i/b^(j+1) := Finset.sum_le_sum hpoint
      _ = (∑ i ∈ band j, x i)/b^(j+1) := by rw [Finset.sum_div]
      _ ≤ K*a^j/b^(j+1) := div_le_div_of_nonneg_right hmass' (pow_nonneg hb.le _)
      _ = (K/b)*r^j := by dsimp [r]; rw [div_pow, pow_succ]; field_simp [hb.ne', pow_ne_zero j hb.ne'] <;> ring
  have hcover (i : I) (hi : i ∈ s) : (x i)^p ≤
      ∑ j ∈ Finset.range N, if i ∈ band j then (x i)^p else 0 := by
    rcases hN i hi with hz | hcut
    · simp [hz, Real.zero_rpow hp.ne']
    · obtain ⟨j, hj, hlo, hhi⟩ := v40_dyadic_band (x i) (hx i hi).2 N hcut
      have hjm : i ∈ band j := Finset.mem_filter.mpr ⟨hi, hlo, hhi⟩
      have hh := Finset.single_le_sum
        (f := fun j => if i ∈ band j then (x i)^p else 0)
        (fun k _ => by split_ifs <;> positivity) (Finset.mem_range.mpr hj)
      simpa only [if_pos hjm] using hh
  have hsum : (∑ i ∈ s, (x i)^p) ≤ ∑ j ∈ Finset.range N, (K/b)*r^j := by
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ Finset.range N, if i ∈ band j then (x i)^p else 0 :=
        Finset.sum_le_sum hcover
      _ = ∑ j ∈ Finset.range N, ∑ i ∈ band j, (x i)^p := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [band]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        simp [hi]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hband j)
  have hgeom : (∑ j ∈ Finset.range N, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    rw [geom_sum_mul]
    linarith [pow_nonneg hr N]
  change (∑ i ∈ s, (x i)^p) ≤ K/(b*(1-r))
  calc
    _ ≤ (K/b)*(∑ j ∈ Finset.range N, r^j) := by rwa [Finset.mul_sum]
    _ ≤ (K/b)*(1/(1-r)) := mul_le_mul_of_nonneg_left hgeom (div_nonneg hK hb.le)
    _ = _ := by field_simp [hb.ne', (sub_pos.mpr hr1).ne'] <;> ring

/-- Unnormalized scale-count version of (36) -> (34). This connects the
normalized density proof to actual N_s and M rather than asking the
caller to supply an already normalized hypothesis. -/
theorem v40_scale_density_power {I : Type*} (s : Finset I) (N : I → ℝ)
    (M p c K : ℝ) (hM : 0 < M) (hp : 0 < p) (hp1 : p < 1) (hc : 1-p < c)
    (hK : 0 ≤ K) (hN : ∀ i ∈ s, 0 ≤ N i ∧ N i ≤ M^2)
    (hmass : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∑ i ∈ s.filter (fun i => N i ≤ δ*M^2), N i) ≤ K*δ^c*M^2) :
    (∑ i ∈ s, (N i)^p) ≤
      (M^2)^p * (K/((1/2:ℝ)^(1-p)*(1-(1/2:ℝ)^c/(1/2:ℝ)^(1-p)))) := by
  classical
  let x := fun i => N i/M^2
  have hM2 : 0 < M^2 := sq_pos_of_pos hM
  have hx (i : I) (hi : i ∈ s) : 0 ≤ x i ∧ x i ≤ 1 := by
    constructor
    · exact div_nonneg (hN i hi).1 hM2.le
    · exact (div_le_iff₀ hM2).mpr (by simpa using (hN i hi).2)
  have hmass' (j : ℕ) :
      (∑ i ∈ s.filter (fun i => x i ≤ (1/2:ℝ)^j), x i) ≤ K*((1/2:ℝ)^c)^j := by
    let δ := (1/2:ℝ)^j
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ1 : δ ≤ 1 := half_pow_le_one j
    have heq : s.filter (fun i => x i ≤ δ) = s.filter (fun i => N i ≤ δ*M^2) := by
      ext i
      simp [x, div_le_iff₀ hM2]
    change (∑ i ∈ s.filter (fun i => x i ≤ δ), N i/M^2) ≤ _
    rw [heq, Finset.sum_div, ← half_rpow_nat]
    apply (div_le_iff₀ hM2).mpr
    exact hmass δ hδ hδ1
  have h := v40_density_to_power s x p c K hp hp1 hc hK hx hmass'
  calc
    _ = (M^2)^p*(∑ i ∈ s, (x i)^p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Real.mul_rpow hM2.le (hx i hi).1]
      have he : M^2*x i = N i := by dsimp [x]; field_simp [hM.ne']
      rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hM2.le _)

end OpenAI086
