import Mathlib
import OpenAI086.PaperCompressionMoments

/-! The logarithmic representative-energy argument on p.11, in two
steps: doubling along a path, and integrating the low/high split.
The actual stopping-tree construction and pointwise support partition
remain separate obligations. -/
namespace OpenAI086
open MeasureTheory

/-- Descending stopping averages (read a spatial path backwards). -/
inductive V38Doubling : List ℝ → Prop
  | nil : V38Doubling []
  | single (a : ℝ) (ha : 0 ≤ a) : V38Doubling [a]
  | cons (a b : ℝ) (l : List ℝ) (hb : 0 ≤ b) (hab : 2*b ≤ a)
      (h : V38Doubling (b::l)) : V38Doubling (a::b::l)

/-- Sum of the descending doubling chain is at most twice its head. -/
theorem v38_doubling_sum (l : List ℝ) (h : V38Doubling l) :
    l.sum ≤ 2*l.headD 0 := by
  induction h with
  | nil => simp
  | single a ha => simp <;> linarith
  | cons a b l hb hab h ih =>
      simp only [List.sum_cons, List.headD_cons] at ih ⊢
      linarith

/-- If every entry is at least t, a chain of length n+1 has head at
least 2^n t. This yields the high-root count by logarithms. -/
theorem v38_doubling_length (l : List ℝ) (h : V38Doubling l)
    (t : ℝ) (ht : ∀ a ∈ l, t ≤ a) :
    (2:ℝ)^(l.length-1)*t ≤ l.headD 0 ∨ l = [] := by
  induction h with
  | nil => exact Or.inr rfl
  | single a ha =>
      left
      simpa using ht a (by simp)
  | cons a b l hb hab h ih =>
      left
      have ht' : ∀ x ∈ b::l, t ≤ x := fun x hx => ht x (by simp [hx])
      rcases ih ht' with hsmall | hempty
      · have h0 : (2:ℝ)^l.length*t ≤ b := by simpa using hsmall
        simp only [List.length_cons, Nat.add_sub_cancel, List.headD_cons]
        rw [pow_succ]
        linarith
      · simp at hempty

/-- A pointwise split over all representatives. Low roots cost an
absolute sum; for each high root use ab ≤ (a²+b²)/2. The high subset
may depend on the spatial point. -/
theorem v38_split_pointwise {K : Type*} [Fintype K] [DecidableEq K]
    (H : Finset K) (p g : K → ℝ) (f M D L : ℝ)
    (hf : 0 ≤ f) (hM : 0 ≤ M) (hD : 0 < D)
    (hp : ∀ k, p k ≤ f*g k)
    (hlow : (∑ k ∈ Finset.univ \ H, g k) ≤ 2*D⁻¹^2*M)
    (hcard : (H.card:ℝ) ≤ L) :
    (∑ k, p k) ≤ 2*D⁻¹^2*f*M + (∑ k, (g k)^2)/2 + L*f^2/2 := by
  classical
  have h1 : (∑ k ∈ Finset.univ \ H, p k) ≤ 2*D⁻¹^2*f*M := by
    calc
      _ ≤ ∑ k ∈ Finset.univ \ H, f*g k := Finset.sum_le_sum (fun k _ => hp k)
      _ = f*(∑ k ∈ Finset.univ \ H, g k) := by rw [Finset.mul_sum]
      _ ≤ f*(2*D⁻¹^2*M) := mul_le_mul_of_nonneg_left hlow hf
      _ = _ := by ring
  have h2 : (∑ k ∈ H, p k) ≤ (∑ k ∈ H, (g k)^2)/2 + (H.card:ℝ)*f^2/2 := by
    calc
      _ ≤ ∑ k ∈ H, ((g k)^2/2+f^2/2) := by
        apply Finset.sum_le_sum
        intro k _
        nlinarith [hp k, sq_nonneg (g k-f)]
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_div] <;> ring
  have h3 : (∑ k ∈ H, (g k)^2) ≤ ∑ k, (g k)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun k _ _ => sq_nonneg (g k))
  have h4 := mul_le_mul_of_nonneg_right hcard (sq_nonneg f)
  have he : (∑ k ∈ Finset.univ \ H, p k) + (∑ k ∈ H, p k) = ∑ k, p k :=
    Finset.sum_sdiff (Finset.subset_univ H)
  linarith

/-- Integrate the pointwise low/high splitting inequality on a genuine
measure space. Uses Young's inequality f M ≤ f²+M²/4 and the L² maximal
estimate, so the final coefficient is exactly 8 D^-2 + L. -/
theorem v38_integrated_representative_energy {Ω K : Type*} [MeasurableSpace Ω]
    [Fintype K] [DecidableEq K] (μ : Measure Ω)
    (f M : Ω → ℝ) (g p : K → Ω → ℝ) (H : Ω → Finset K) (D L : ℝ)
    (hD : 0 < D) (hf : ∀ x, 0 ≤ f x) (hM : ∀ x, 0 ≤ M x)
    (hp : ∀ x k, p k x ≤ f x*g k x)
    (hlow : ∀ x, (∑ k ∈ Finset.univ \ H x, g k x) ≤ 2*D⁻¹^2*M x)
    (hcard : ∀ x, ((H x).card:ℝ) ≤ L)
    (hfi : Integrable (fun x => (f x)^2) μ)
    (hMi : Integrable (fun x => (M x)^2) μ)
    (hgi : ∀ k, Integrable (fun x => (g k x)^2) μ)
    (hpi : ∀ k, Integrable (p k) μ)
    (hmoment : ∀ k, (∫ x, p k x ∂μ) = ∫ x, (g k x)^2 ∂μ)
    (hmax : (∫ x, (M x)^2 ∂μ) ≤ 4*(∫ x, (f x)^2 ∂μ)) :
    (∑ k, ∫ x, (g k x)^2 ∂μ) ≤ (8*D⁻¹^2+L)*(∫ x, (f x)^2 ∂μ) := by
  classical
  let S := ∑ k, ∫ x, (g k x)^2 ∂μ
  let F := ∫ x, (f x)^2 ∂μ
  let A := ∫ x, (M x)^2 ∂μ
  let c := 2*D⁻¹^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (x : Ω) : (∑ k, p k x) ≤
      c*(f x)^2+c/4*(M x)^2+(∑ k, (g k x)^2)/2+L/2*(f x)^2 := by
    have h := v38_split_pointwise (H x) (fun k => p k x) (fun k => g k x)
      (f x) (M x) D L (hf x) (hM x) hD (hp x) (hlow x) (hcard x)
    have hy : f x*M x ≤ (f x)^2+(M x)^2/4 := by nlinarith [sq_nonneg (f x-M x/2)]
    have hy' := mul_le_mul_of_nonneg_left hy hc
    change (∑ k, p k x) ≤ c*f x*M x+(∑ k, (g k x)^2)/2+L*(f x)^2/2 at h
    linarith
  have hsumg : Integrable (fun x => ∑ k, (g k x)^2) μ := integrable_finset_sum _ (fun k _ => hgi k)
  have hsump : Integrable (fun x => ∑ k, p k x) μ := integrable_finset_sum _ (fun k _ => hpi k)
  have hir : Integrable (fun x => c*(f x)^2+c/4*(M x)^2+
      (∑ k, (g k x)^2)/2+L/2*(f x)^2) μ := by
    have h := (((hfi.const_mul c).add (hMi.const_mul (c/4))).add
      (hsumg.const_mul (1/2:ℝ))).add (hfi.const_mul (L/2))
    convert h using 1 <;> ext x <;> ring
  have hi := integral_mono hsump hir hpoint
  have hleft : (∫ x, ∑ k, p k x ∂μ) = S := by
    rw [integral_finset_sum _ (fun k _ => hpi k)]
    exact Finset.sum_congr rfl (fun k _ => hmoment k)
  have hright : (∫ x, c*(f x)^2+c/4*(M x)^2+
      (∑ k, (g k x)^2)/2+L/2*(f x)^2 ∂μ) = c*F+c/4*A+S/2+L/2*F := by
    have hd : Integrable (fun x => (∑ k, (g k x)^2)/2) μ := by
      convert hsumg.const_mul (1/2:ℝ) using 1 <;> ext x <;> ring
    rw [integral_add (((hfi.const_mul c).add (hMi.const_mul (c/4))).add hd) (hfi.const_mul (L/2)),
      integral_add ((hfi.const_mul c).add (hMi.const_mul (c/4))) hd,
      integral_add (hfi.const_mul c) (hMi.const_mul (c/4)),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_div, integral_finset_sum _ (fun k _ => hgi k)] <;> rfl
  rw [hleft, hright] at hi
  have hh : A ≤ 4*F := hmax
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ c/4 by positivity)
  change S ≤ (8*D⁻¹^2+L)*F
  dsimp [c] at hi hm
  nlinarith

end OpenAI086
