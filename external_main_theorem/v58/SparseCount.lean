import TrilinearHT.Auto.Sec15_3FiniteSparseCountLemma

/-! Paper Lemma 9.1, p.82: reference-backed proof using the stronger
quantitative bound of the pinned Joris Roos reference. All geometric
hypotheses are retained, including the side budget and pure-shift gap.
The zero-filled tuple convention represents the core product; the
reference definition Auto.roleCoeff is used. This is an adapted proof,
not a replay of every geometric step in the printed paper. -/
namespace OpenAI086.ReferenceV58
open scoped BigOperators

theorem lemma91 :
    ∀ (d : ℕ) (ζ : Fin d → ℝ) (core : Finset (Fin 4)), (core.card = 3 ∨ core.card = 4) →
    ∀ (A : Fin 4 → Finset ℝ) (M L : ℝ), 1 ≤ M → 1 ≤ L → (∀ i ∈ core, ((A i).card : ℝ) ≤ M) →
    ∀ (B Sg Q μ ν R₀ : ℝ), 1 ≤ B → 0 < μ → μ ≤ 1 → 1 ≤ ν → 0 < R₀ →
    ∀ (S : Finset ℤ) (E : ℤ → Finset (Fin 4 → ℝ)),
    (∀ s ∈ S, ∀ x ∈ E s, (∀ i ∈ core, x i ∈ A i) ∧ ∀ i ∉ core, x i = 0) →
    (∀ i ∈ core, ∀ j ∈ core, i ≠ j → ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s',
      x i = x' i → x j = x' j → x = x') →
    (∀ x, ((S.filter fun s => x ∈ E s).card : ℝ) ≤ L) →
    (core.card = 3 → ∃ w : ℤ → ℝ, (∀ s, 0 ≤ w s) ∧ ∑ s ∈ S, w s ≤ M ∧
      ∀ s ∈ S, ∀ i ∈ core, ∀ a, (((E s).filter fun x => x i = a).card : ℝ) ≤ w s) →
    (∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', x i ≠ x' i →
      ∀ n : Fin d → ℤ, (∀ k, |(n k : ℝ)| ≤ Q) →
        Sg * max (R₀ * 2 ^ s) (R₀ * 2 ^ s') < |x i - x' i + ∑ k, (n k : ℝ) * ζ k|) →
    (∀ T ⊆ core, T.card = 3 → ∀ l, l ∉ T → ∀ s ∈ S, ∀ x ∈ E s, ∃ n : Fin d → ℤ,
      (∀ k, |(n k : ℝ)| ≤ B) ∧
        μ * (R₀ * 2 ^ s) ≤ |∑ i ∈ T, (Auto.roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k| ∧
        |∑ i ∈ T, (Auto.roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k| ≤ ν * (R₀ * 2 ^ s)) →
    (∀ s ∈ S, (E s).Nonempty → ∀ n : Fin d → ℤ, (∀ k, |(n k : ℝ)| ≤ Q) →
      |∑ k, (n k : ℝ) * ζ k| ∉ Set.Icc (μ * (R₀ * 2 ^ s) / 1000) (1000 * ν * (R₀ * 2 ^ s))) →
    7200000 * ((d : ℝ) + 1) ^ 2 * B ≤ Q → 7200000 * ((d : ℝ) + 1) ^ 2 * ν ≤ Sg →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∑ s ∈ S.filter (fun s => ((E s).card : ℝ) ≤ δ * M ^ 2), ((E s).card : ℝ) ≤
        3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * ν / μ)) * L ^ 29 *
          δ ^ (1 / 2080 : ℝ) * M ^ 2 := by
  intro d ζ core hcore A M L hM hL hA B Sg Q μ ν R₀ hB hμ hμ1 hν hR₀ S E hE hpair hmult hside
    hsep hann hgap hQ hSg δ hδ0 hδ1
  have h := Auto.sparse_count_explicit d ζ core hcore A M L hM hL hA
    B Sg Q μ ν R₀ hB hμ hμ1 hν hR₀ S E hE hpair hmult hside
    hsep hann hgap hQ hSg δ hδ0 hδ1
  have hLpow : L^12 ≤ L^29 := by
    calc
      L^12 = L^12 * 1 := by ring
      _ ≤ L^12 * L^17 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) (by positivity)
      _ = L^29 := by rw [← pow_add]; norm_num
  have hδpow : δ ^ (1/300 : ℝ) ≤ δ ^ (1/2080 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by norm_num)
  have he : 0 ≤ 1 + Real.logb 2 (2 + ((d : ℝ) + 1)^2 * ν / μ) := by
    have hlog : 0 ≤ Real.logb 2 (2 + ((d : ℝ) + 1)^2 * ν / μ) := by
      apply Real.logb_nonneg (by norm_num)
      have : 0 ≤ ((d : ℝ) + 1)^2 * ν / μ := by positivity
      linarith
    linarith
  have hC : 0 ≤ (3 * 10 ^ 11 : ℝ) *
      (1 + Real.logb 2 (2 + ((d : ℝ) + 1)^2 * ν / μ)) :=
    mul_nonneg (by norm_num) he
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hLpow hC) hδpow
      (Real.rpow_nonneg hδ0.le _) (by positivity)) (sq_nonneg M)

end OpenAI086.ReferenceV58
#print axioms OpenAI086.ReferenceV58.lemma91
