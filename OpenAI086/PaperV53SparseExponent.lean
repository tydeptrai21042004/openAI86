import OpenAI086.PaperV53ParameterCompletion

/-! Lemma 9.1 p.87: optimize the auxiliary powers in the last paragraph.
The preceding geometric counting inequality remains an explicit premise.
This closes the numerical optimization, including the large-density case. -/
namespace OpenAI086

/-- The exact choices of auxiliary parameters and their three powers. -/
theorem v53_sparse_auxiliary_powers (δ : ℝ) (hd : 0 < δ) :
    let α := δ^(1/1040:ℝ)
    let κ := α*α
    κ/α = δ^(1/1040:ℝ) ∧
    Real.sqrt α = δ^(1/2080:ℝ) ∧
    α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ) = δ^(1/20:ℝ) := by
  dsimp
  have ha : 0 < δ^(1/1040:ℝ) := Real.rpow_pos_of_pos hd _
  refine ⟨?_, ?_, ?_⟩
  · field_simp [ha.ne']
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd.le]
    congr 1
    norm_num
  · have hk : δ^(1/1040:ℝ)*δ^(1/1040:ℝ) = δ^(2/1040:ℝ) := by
      rw [← Real.rpow_add hd]
      congr 1
      norm_num
    rw [hk, ← Real.rpow_mul hd.le, ← Real.rpow_mul hd.le,
        ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    norm_num

/-- The small-density geometric estimate from p.87 implies the desired
saving with explicit constant 3*C. No bound on the number of scales. -/
theorem v53_sparse_small_density (δ L ell C mass : ℝ)
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hL : 1 ≤ L) (hell : 1 ≤ ell) (hC : 0 ≤ C)
    (hgeom : let α := δ^(1/1040:ℝ); let κ := α*α;
      mass ≤ C*(L*κ/α + Real.sqrt (L*α) + ell*L^29*α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ))) :
    mass ≤ 3*C*ell*L^29*δ^(1/2080:ℝ) := by
  let α := δ^(1/1040:ℝ)
  let κ := α*α
  have ha : 0 < α := Real.rpow_pos_of_pos hd _
  have hLn : 0 ≤ L := by linarith
  have helln : 0 ≤ ell := by linarith
  obtain ⟨hfirst,hroot,hlast⟩ := v53_sparse_auxiliary_powers δ hd
  change κ/α = δ^(1/1040:ℝ) at hfirst
  change Real.sqrt α = δ^(1/2080:ℝ) at hroot
  change α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ) = δ^(1/20:ℝ) at hlast
  change mass ≤ C*(L*κ/α + Real.sqrt (L*α) + ell*L^29*α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ)) at hgeom
  have hLp : L ≤ L^29 := by
    calc
      L = L*1 := by ring
      _ ≤ L*L^28 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) (by linarith)
      _ = L^29 := by ring
  have hLe : L ≤ ell*L^29 := by
    calc
      L ≤ L^29 := hLp
      _ = 1*L^29 := by ring
      _ ≤ ell*L^29 := mul_le_mul_of_nonneg_right hell (by positivity)
  have hsqrt : Real.sqrt L ≤ L := by
    have hs := Real.sq_sqrt hLn
    have hs0 := Real.sqrt_nonneg L
    have hs1 : 1 ≤ Real.sqrt L := by
      by_contra! h
      nlinarith [mul_nonneg hs0 (show 0 ≤ 1-Real.sqrt L by linarith)]
    nlinarith [mul_nonneg hs0 (show 0 ≤ Real.sqrt L-1 by linarith)]
  have hpow1 := v53_small_base_power δ (1/2080) (1/1040) hd hd1 (by norm_num)
  have hpow2 := v53_small_base_power δ (1/2080) (1/20) hd hd1 (by norm_num)
  have hmain1 : L*κ/α ≤ ell*L^29*δ^(1/2080:ℝ) := by
    rw [mul_div_assoc, hfirst]
    exact mul_le_mul hLe hpow1 (Real.rpow_nonneg hd.le _) (by positivity)
  have hmain2 : Real.sqrt (L*α) ≤ ell*L^29*δ^(1/2080:ℝ) := by
    rw [Real.sqrt_mul (by linarith : 0 ≤ L), hroot]
    exact mul_le_mul_of_nonneg_right (hsqrt.trans hLe) (Real.rpow_nonneg hd.le _)
  have hmain3 : ell*L^29*α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ) ≤
      ell*L^29*δ^(1/2080:ℝ) := by
    calc
      _ = (ell*L^29)*(α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ)) := by ring
      _ = ell*L^29*δ^(1/20:ℝ) := by rw [hlast]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow2 (by positivity)
  calc
    _ ≤ C*(L*κ/α + Real.sqrt (L*α) + ell*L^29*α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ)) := hgeom
    _ ≤ C*(3*(ell*L^29*δ^(1/2080:ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring

/-- The remaining-density argument in the paper: combine the small-density
estimate with the global L bound for normalized mass. The chosen cutoff
may be any positive number at most one, fixed independently of scales. -/
theorem v53_sparse_all_density (δ δ0 L ell C mass : ℝ)
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hcut : 0 < δ0) (hcut1 : δ0 ≤ 1)
    (hL : 1 ≤ L) (hell : 1 ≤ ell) (hC : 0 ≤ C) (htotal : mass ≤ L)
    (hsmall : δ ≤ δ0 → let α := δ^(1/1040:ℝ); let κ := α*α;
      mass ≤ C*(L*κ/α + Real.sqrt (L*α) + ell*L^29*α^(-4:ℝ)*κ^(-24:ℝ)*δ^(1/10:ℝ))) :
    mass ≤ max (3*C) (δ0^(-1/2080:ℝ))*ell*L^29*δ^(1/2080:ℝ) := by
  have hLn : 0 ≤ L := by linarith
  have helln : 0 ≤ ell := by linarith
  by_cases h : δ ≤ δ0
  · have hs := v53_sparse_small_density δ L ell C mass hd hd1 hL hell hC (hsmall h)
    calc
      _ ≤ 3*C*ell*L^29*δ^(1/2080:ℝ) := hs
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) helln)
          (pow_nonneg hLn _)) (Real.rpow_nonneg hd.le _)
  · have hLpos : 0 ≤ L := by linarith
    have hLp : L ≤ ell*L^29 := by
      calc
        L = L*1 := by ring
        _ ≤ L*L^28 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) hLpos
        _ = 1*L^29 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hell (by positivity)
    have hp : δ0^(1/2080:ℝ) ≤ δ^(1/2080:ℝ) :=
      Real.rpow_le_rpow hcut.le (le_of_not_ge h) (by norm_num)
    have hinv : 1 ≤ δ0^(-1/2080:ℝ)*δ^(1/2080:ℝ) := by
      calc
        1 = δ0^(-1/2080:ℝ)*δ0^(1/2080:ℝ) := by
          rw [← Real.rpow_add hcut]
          norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hcut.le _)
    calc
      _ ≤ L := htotal
      _ ≤ ell*L^29 := hLp
      _ = (ell*L^29)*1 := by ring
      _ ≤ (ell*L^29)*(δ0^(-1/2080:ℝ)*δ^(1/2080:ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = δ0^(-1/2080:ℝ)*ell*L^29*δ^(1/2080:ℝ) := by ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) helln)
          (pow_nonneg hLn _)) (Real.rpow_nonneg hd.le _)

end OpenAI086
