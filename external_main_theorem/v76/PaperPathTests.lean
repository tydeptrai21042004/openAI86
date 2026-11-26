/-
Adapted from the pinned Joris Roos reference (Apache-2.0),
Sec13_5RepresentativesComponentSizesFirstTops and Sec15_4VerificationCountingHypotheses.
V76: paper-specific representative tests and actual side-window bounds.
Uncompiled proof candidates.
-/
import ReferenceV76PaperTorus

set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace Auto
open MeasureTheory Metric OpenAI086.AdaptedV56 OpenAI086.ReferenceV70
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

open Classical in
/-- The separation theorem only needs the two tested pre-cells to contain x*.
Other nodes of the global type class may be on disjoint spatial branches. -/
theorem paper_pair_label_sep {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    (hΛ : 8 * Ms.Λ ≤ S.Ξ) {xs : ℝ} {c c' : ℤ × (ℤ × ℤ) × Ms.Md}
    (hc : c ∈ R.Nd) (hc' : c' ∈ R.Nd)
    (hxc : xs ∈ dyadicGridCell Gd c.2.1.1 c.2.1.2)
    (hxc' : xs ∈ dyadicGridCell Gd c'.2.1.1 c'.2.1.2)
    (hne : R.rep c ≠ R.rep c')
    (n : Fin Ms.zc.dim → ℤ) (hn : ∀ i, |(n i : ℝ)| ≤ S.Eh h)
    {rI rI' : ℝ} (hrI : dyadicGridLength Gd (max c.1 c'.1 + S.K) ≤ rI)
    (hrI' : dyadicGridLength Gd (max c.1 c'.1 + S.K) ≤ rI') :
    S.Ξ / 2 * max rI⁻¹ rI'⁻¹ < |Ms.slope (R.rep c) xs - Ms.slope (R.rep c') xs +
      (∑ i, (n i : ℝ) * (Ms.zc.θ i / S.Q0)) / ModeSchedule.Lh h| := by
  let Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md) := {c, c'}
  have hsub : Nd ⊆ R.Nd := by
    intro x hx
    simp only [Nd, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hc
    · exact hc'
  have halive : ∀ x ∈ Nd, x.2.2 ∈ Ms.alive (ancAt Gd x.2.1 (x.1 - 4 * S.K)) :=
    fun x hx => R.halive x (hsub hx)
  have hd : ∀ x (hx : x ∈ Nd) y (hy : y ∈ Nd) (h1 : x.1 = y.1) (h2 : x.2.1 = y.2.1),
      x ≠ y → (⟨y.2.2, by rw [h1, h2]; exact halive y hy⟩ :
        Ms.alive (ancAt Gd x.2.1 (x.1 - 4 * S.K))) ∉
        (Ms.blockComps S hA x.1 x.2.1).F h ⟨x.2.2, halive x hx⟩ := by
    intro x hx y hy h1 h2 hxy
    exact R.hdist x (hsub hx) y (hsub hy) h1 h2 hxy
  have hsep : ∀ x y, nodeLt3 (Gd := Gd) Ms Nd x y → R.rep x ≠ R.rep y →
      ∀ z z' : Ms.alive (ancAt Gd y.2.1 (y.1 - 4 * S.K)),
      z.1 ∈ Ms.predOfMode S hA Δ h x → z'.1 ∈ Ms.predOfMode S hA Δ h y →
      z ∉ (Ms.blockComps S hA y.1 y.2.1).F h z' := by
    intro x y hxy hne' z z' hz hz'
    exact R.hsepP x y ⟨hsub hxy.1, hsub hxy.2.1, hxy.2.2.1, hxy.2.2.2⟩ hne' z z' hz hz'
  have hxs : ∀ x ∈ Nd, xs ∈ dyadicGridCell Gd x.2.1.1 x.2.1.2 := by
    intro x hx
    simp only [Nd, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hxc
    · exact hxc'
  exact Ms.role_label_separation3 S hA Nd (fun x hx => R.hNd x (hsub hx)) Δ h halive hd
    R.rep R.hrep hsep hΛ hxs (by simp [Nd]) (by simp [Nd]) hne n hn hrI hrI'

end ModeSystem
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}
namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Actual cell-scale shifted-frequency gap for a fixed paper representative type.
The shift normalization is exactly the zetaVec used in the sparse-count theorem. -/
theorem paper_path_label_sep (G : bf.Grp) (j : Fin 4) (h : ℕ)
    (R : (D.Ms j G).PaperRepClass D.S D.hA D.SP D.SP.Δ h)
    (hΛ : 8 * (D.Ms j G).Λ ≤ D.S.Ξ) (I I' : ℤ × ℤ)
    (m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (m' : (D.Ms j G).alive (ancAt A.G (D.preAt I') (A.blkStart D.S.K I'.1 - 4 * D.S.K)))
    (hm : (A.blkStart D.S.K I.1, D.preAt I, m.1) ∈ R.Nd)
    (hm' : (A.blkStart D.S.K I'.1, D.preAt I', m'.1) ∈ R.Nd)
    {xs : ℝ} (hx : xs ∈ dyadicGridCell A.G I.1 I.2)
    (hx' : xs ∈ dyadicGridCell A.G I'.1 I'.2)
    (hne : (D.Ms j G).slope (R.rep (A.blkStart D.S.K I.1, D.preAt I, m.1)) xs ≠
      (D.Ms j G).slope (R.rep (A.blkStart D.S.K I'.1, D.preAt I', m'.1)) xs)
    {Q : ℝ} (hcQ : ((6 ^ 8 : ℕ) : ℝ) * Q ≤ D.S.Eh h)
    (N : Fin (D.Ms j G).zc.dim → ℤ) (hN : ∀ i, |(N i : ℝ)| ≤ Q) :
    D.S.Ξ / 2 * max (dyadicGridLength A.G I.1)⁻¹ (dyadicGridLength A.G I'.1)⁻¹ <
      |(D.Ms j G).slope (R.rep (A.blkStart D.S.K I.1, D.preAt I, m.1)) xs -
        (D.Ms j G).slope (R.rep (A.blkStart D.S.K I'.1, D.preAt I', m'.1)) xs +
        ∑ k, (N k : ℝ) * zetaVec (D.Ms j G).zc D.S.Q0 h k| := by
  have hrepne : R.rep (A.blkStart D.S.K I.1, D.preAt I, m.1) ≠
      R.rep (A.blkStart D.S.K I'.1, D.preAt I', m'.1) := fun he => hne (by rw [he])
  let M : Fin (D.Ms j G).zc.dim → ℤ := fun k => (6 ^ 8 : ℤ) * N k
  have hM : ∀ k, |(M k : ℝ)| ≤ D.S.Eh h := by
    intro k
    dsimp [M]
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 ^ 8)]
    exact (mul_le_mul_of_nonneg_left (hN k) (by positivity)).trans (by exact_mod_cast hcQ)
  have hb := blkStart_bounds D.hK I.1 (A := A)
  have hb' := blkStart_bounds D.hK I'.1 (A := A)
  have hlen : dyadicGridLength A.G (max (A.blkStart D.S.K I.1) (A.blkStart D.S.K I'.1) + D.S.K) ≤
      dyadicGridLength A.G I.1 := (dyadicGridLength_strictAnti A.G).antitone
      (by have := le_max_left (A.blkStart D.S.K I.1) (A.blkStart D.S.K I'.1); omega)
  have hlen' : dyadicGridLength A.G (max (A.blkStart D.S.K I.1) (A.blkStart D.S.K I'.1) + D.S.K) ≤
      dyadicGridLength A.G I'.1 := (dyadicGridLength_strictAnti A.G).antitone
      (by have := le_max_right (A.blkStart D.S.K I.1) (A.blkStart D.S.K I'.1); omega)
  have hs := (D.Ms j G).paper_pair_label_sep D.S D.hA D.SP R hΛ hm hm'
    (D.subset_preAt I hx) (D.subset_preAt I' hx') hrepne M hM hlen hlen'
  have he : (∑ k, (M k : ℝ) * ((D.Ms j G).zc.θ k / D.S.Q0)) / ModeSchedule.Lh h =
      ∑ k, (N k : ℝ) * zetaVec (D.Ms j G).zc D.S.Q0 h k := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold M zetaVec
    push_cast
    ring
  rw [he] at hs
  exact hs

/-- The actual paper-side Fourier windows, including the special U slot, depend only
on the physical coordinate and satisfy the normalized Bessel bound. -/
theorem paper_window_root_le (G : bf.Grp) (I : ℤ × ℤ) (l : Fin 4) (K : Finset ℤ) :
    Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys (D.paperSideAt l G I))
      (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) K ρ'
      ∂offsetMeasure (D.Ms 0 G).zc.dim) ≤
    Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys (D.paperSideAt l G I) y‖ ^ 2) :=
  window_root_le (D.Ms 0 G).zc l (D.paperSideAt l G I) I K

end SideInput
end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ModeSystem.paper_pair_label_sep
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_path_label_sep
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.paper_window_root_le
