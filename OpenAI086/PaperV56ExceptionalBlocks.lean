import OpenAI086.PaperV41Section3

/-! Lemma 8.2, first assertion. Apply the logarithmic packet cover from
Lemma 3.5(1) to the actual K-spaced block schedule. The erroneous printed
scale-count assertion 3.5(2) is not used. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- A family of finite log packets with radius W/2 covers every exceptional
block index by at most a length-four interval in block-index coordinates. -/
theorem v56_packet_exceptional_count (P : Finset ℝ) (N : Finset ℤ)
    (K W τ b₀ : ℝ) (hK : 0 < K) (hW : 0 ≤ W) (hτ : 0 ≤ τ)
    (hw : W + 2*τ ≤ K)
    (he : ∀ n ∈ N, ∃ p ∈ P, ∃ x : ℝ,
      |x-p| ≤ W/2 ∧
      b₀ + K*(n:ℝ) - 2*K - τ < x ∧
      x < b₀ + K*(n:ℝ) + K + τ) :
    (N.card : ℝ) ≤ 5*(P.card : ℝ) := by
  have hcover : ∀ n ∈ N, ∃ p ∈ P,
      (p-W/2-b₀-K-τ)/K ≤ (n:ℝ) ∧
      (n:ℝ) ≤ (p+W/2-b₀+2*K+τ)/K := by
    intro n hn
    obtain ⟨p,hp,x,hx,hlo,hhi⟩ := he n hn
    rw [abs_le] at hx
    refine ⟨p,hp,(div_le_iff₀ hK).mpr ?_,(le_div_iff₀ hK).mpr ?_⟩ <;> nlinarith
  have hab : ∀ p ∈ P, (p-W/2-b₀-K-τ)/K ≤ (p+W/2-b₀+2*K+τ)/K := by
    intro p _
    apply div_le_div_of_nonneg_right _ hK.le
    linarith
  have hwidth : ∀ p ∈ P,
      (p+W/2-b₀+2*K+τ)/K - (p-W/2-b₀-K-τ)/K ≤ 4+0 := by
    intro p _
    rw [← sub_div]
    apply (div_le_iff₀ hK).mpr
    linarith
  have h := v31_corrected_packet_count P
    (fun p => (p-W/2-b₀-K-τ)/K) (fun p => (p+W/2-b₀+2*K+τ)/K)
    4 0 N (by norm_num) (by norm_num) hab hwidth hcover
  linarith

/-- The actual rational-height evaluations of one primary can cause at
most 5d exceptional blocks, independently of the depth range or size
of the real frequencies. The translated packet cover is constructed,
not supplied as a hypothesis. `shift` is log₂ r₀ in the paper. -/
theorem v56_primary_exceptional_blocks (d B : ℕ) (ξ : Fin d → ℝ)
    (N : Finset ℤ) (K τ b₀ shift : ℝ) (hK : 0 < K) (hτ : 0 ≤ τ)
    (hw : 2*v34Width d B + 2*τ ≤ K)
    (he : ∀ n ∈ N, ∃ v, v34HeightValue d B ξ v ∧
      b₀ + K*(n:ℝ)-2*K-τ < Real.log v / Real.log 2 + shift ∧
      Real.log v / Real.log 2 + shift < b₀ + K*(n:ℝ)+K+τ) :
    (N.card : ℝ) ≤ 5*(d:ℝ) := by
  classical
  obtain ⟨P,hP,hc⟩ := v34_height_log_cover d B ξ
  let Q := P.image (fun p => p+shift)
  have hQ : Q.card ≤ d := (Finset.card_image_le).trans hP
  have h := v56_packet_exceptional_count Q N K (2*v34Width d B) τ b₀ hK
    (mul_nonneg (by norm_num) (v34_width_nonneg d B)) hτ hw (by
      intro n hn
      obtain ⟨v,hv,hlo,hhi⟩ := he n hn
      obtain ⟨p,hp,hp'⟩ := hc v hv
      refine ⟨p+shift,Finset.mem_image.mpr ⟨p,hp,rfl⟩,
        Real.log v / Real.log 2 + shift,?_,hlo,hhi⟩
      have hEq : Real.log v / Real.log 2 + shift - (p+shift) =
          Real.log v / Real.log 2-p := by ring
      rw [hEq]
      linarith)
  exact h.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) (by norm_num))

end OpenAI086
