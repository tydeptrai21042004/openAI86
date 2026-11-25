import OpenAI086.PaperCompressionMeasureBridge
import OpenAI086.PaperV43Lemma33

/-! V48: exact arithmetic for the restart cutoff in Lemma 3.4, pp.11--12.
The paper chooses tau=D^-10, b=2D(m+1), and T at least
b^(128(m+1)^2). This file proves the advertised contraction coefficient
is < 1/2 once the logarithmic-envelope estimate L_T <= b^4 is available.
The geometric construction of the anchor partitions remains separate. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- The paper's exponent in the restart cutoff. -/
def v48RestartExponent (m : ℕ) : ℕ := 128*(m+1)^2

/-- The conservative restart factor from the paper (using L_T^(2m),
which is larger than the L_T^(2(m-1)) factor from Lemma 3.3). -/
def v48RestartFactor (D L : ℝ) (m T : ℕ) : ℝ :=
  16*D^32*(m:ℝ)^2*L^(2*m)/(T:ℝ)

/-- For the paper's choices b=2D(m+1) and T>=b^(128(m+1)^2),
the restart factor is strictly below one half whenever L_T<=b^4.
This isolates the numerical absorption from the still-open spatial tree
and variation estimates. -/
theorem v48_restart_factor_lt_half
    (D L b : ℝ) (m T : ℕ)
    (hD : 2 ≤ D) (hm : 1 ≤ m)
    (hb : b = 2*D*((m:ℝ)+1))
    (hL0 : 0 ≤ L) (hL : L ≤ b^4)
    (hT : b^(v48RestartExponent m) ≤ (T:ℝ)) :
    v48RestartFactor D L m T < 1/2 := by
  have hb8 : 8 ≤ b := by rw [hb]; nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hDb : D ≤ b/2 := by rw [hb]; nlinarith
  have hmcast : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmb : (m:ℝ) ≤ b/4 := by rw [hb]; nlinarith
  have hD32 : D^32 ≤ b^32 :=
    pow_le_pow_left₀ (by linarith : 0 ≤ D) hDb 32
  have hm2 : (m:ℝ)^2 ≤ b^2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ (m:ℝ)) (hmb.trans (by linarith)) 2
  have hLpow : L^(2*m) ≤ b^(8*m) := by
    calc
      L^(2*m) ≤ (b^4)^(2*m) :=
        pow_le_pow_left₀ hL0 hL (2*m)
      _ = b^(8*m) := by rw [← pow_mul]; congr 1 <;> omega
  have hprod : D^32*(m:ℝ)^2*L^(2*m) ≤ b^(34+8*m) := by
    calc
      _ ≤ b^32*b^2*b^(8*m) := by
        exact mul_le_mul
          (mul_le_mul hD32 hm2 (by positivity) (by positivity))
          hLpow (by positivity) (by positivity)
      _ = b^(34+8*m) := by
        rw [← pow_add, ← pow_add]
        congr 1 <;> omega
  have hexpR : (34:ℝ)+8*(m:ℝ)+470 ≤ 128*((m:ℝ)+1)^2 := by
    nlinarith [sq_nonneg ((m:ℝ)-1)]
  have hexp : 34+8*m+470 ≤ v48RestartExponent m := by
    dsimp [v48RestartExponent]
    exact_mod_cast hexpR
  let r : ℕ := v48RestartExponent m-(34+8*m)
  have hr : 470 ≤ r := by dsimp [r]; omega
  have hN : v48RestartExponent m = (34+8*m)+r := by
    dsimp [r]; omega
  have hden : b^(34+8*m)*b^r ≤ (T:ℝ) := by
    calc
      _ = b^(v48RestartExponent m) := by rw [← pow_add, hN]
      _ ≤ (T:ℝ) := hT
  have hTpos : 0 < (T:ℝ) := by
    have : 0 < b^(v48RestartExponent m) := by positivity
    exact lt_of_lt_of_le this hT
  have hbr : 0 < b^r := by positivity
  have hratio : b^(34+8*m)/(T:ℝ) ≤ 1/b^r := by
    apply (div_le_iff₀ hTpos).2
    have hh : b^(34+8*m) ≤ (T:ℝ)/b^r :=
      (le_div_iff₀ hbr).2 hden
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hrpow : b^470 ≤ b^r :=
    pow_le_pow_right₀ hb1 hr
  have htail : 1/b^r ≤ 1/b^470 :=
    one_div_le_one_div_of_le (by positivity) hrpow
  have hmain : v48RestartFactor D L m T ≤ 16/b^470 := by
    unfold v48RestartFactor
    calc
      _ ≤ 16*b^(34+8*m)/(T:ℝ) := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        exact mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ 16*(1/b^470) := by nlinarith [hratio, htail]
      _ = 16/b^470 := by ring
  have hpow64 : (64:ℝ) ≤ b^470 := by
    have hb2 : (64:ℝ) ≤ b^2 := by nlinarith
    have hone : 1 ≤ b^468 := one_le_pow₀ hb1
    calc
      _ ≤ b^2 := hb2
      _ = b^2*1 := by ring
      _ ≤ b^2*b^468 := by
        exact mul_le_mul_of_nonneg_left hone (sq_nonneg b)
      _ = b^470 := by rw [← pow_add]; norm_num
  have hquarter : 16/b^470 ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity : 0 < b^470)).2
    nlinarith
  linarith

/-- Exact exponent algebra: the nested-prefix variation factor combined
with G=4D^5, tau=D^-10, and the private-coordinate D^-1 loss has the
D^32 numerator in the manuscript's restart constant. -/
theorem v48_restart_factor_from_variation
    (D L : ℝ) (m T : ℕ)
    (hD : 0 < D) (hT : 0 < T) :
    (m:ℝ)^2*L^(2*(m-1))*16*D^10 /
      ((T:ℝ)*(D⁻¹*(D⁻¹)^10)^2) =
      16*D^32*(m:ℝ)^2*L^(2*(m-1))/(T:ℝ) := by
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hTm : (T:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hinv : D⁻¹*(D⁻¹)^10 = (D⁻¹)^11 := by
    rw [← pow_succ]
    ring
  rw [hinv]
  field_simp [hD0,hTm]
  ring

end OpenAI086
