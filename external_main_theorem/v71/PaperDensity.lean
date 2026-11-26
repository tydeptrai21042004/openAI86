/-!
Section 8.6: exact floor-log bad-density bound on the paper-side events.
Adapted in part from TrilinearHT/Auto/Sec13_3BesselRowsLinearSideEnergy.lean,
Copyright (c) 2026 Joris Roos; original authors: Claude; Apache-2.0.
Unlike the reference ratio-based chain, this uses PaperCore and PaperGood.
-/
import ReferenceV70PaperTypes
import TrilinearHT.Auto.Sec13_3BesselRowsLinearSideEnergy

namespace OpenAI086.ReferenceV71
open Auto OpenAI086.AdaptedV56
open scoped BigOperators

/-- The exceptional set need only be collected at the final height: monotonicity
ensures it covers all exceptional labels encountered at earlier heights. -/
open Classical in
theorem paper_chain_bound {P : Type*} [DecidableEq P] (N J Δ M A B : ℕ)
    (Mode : ℕ → Type*) [∀ i, DecidableEq (Mode i)]
    (C : ∀ i, ModeComponents (Mode i) P) (x : ∀ i, Mode i)
    (good : ℕ → ℕ → P → Prop) [∀ i h, DecidablePred (good i h)]
    (nonexc : ℕ → P → Prop) (δ : ℝ) (hδ : 0 < δ)
    (hlink : ∀ i < N, ∀ h, (C i).labels ((C i).F h (x i)) ⊆
      (C (i+1)).labels ((C (i+1)).E h (x (i+1))))
    (hM : ∀ i h, ((C i).labels ((C i).F h (x i))).card ≤ M)
    (hA : ∀ i p, nonexc i p → ((Finset.range (J+1)).filter fun h => ¬ good i h p).card ≤ A)
    (hB : ∀ p, ((Finset.range (N+1)).filter fun i => ¬ nonexc i p).card ≤ B)
    (hside : ∀ i ≤ N, ¬ (C i).PaperCore Δ (good i) J δ (x i))
    (hbudget : 2*((Δ:ℝ)*(v57FloorLog M+1) + (A:ℝ)*(harmonic M:ℝ)/(1/10)) ≤ δ*(J+1 : ℕ)) :
    ((N+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ) + (B:ℝ)*(harmonic M:ℝ)/(1/10))/δ := by
  classical
  let LE : ℕ → ℕ → Finset P := fun i h => (C i).labels ((C i).E h (x i))
  let LF : ℕ → ℕ → Finset P := fun i h => (C i).labels ((C i).F h (x i))
  let X : ℕ → Finset P := fun i => (LF i J).filter fun p => ¬ nonexc i p
  let Y : ℕ → ℕ → Finset P := fun i h => (LF i h).filter fun p => nonexc i p ∧ ¬ good i h p
  have hEF : ∀ i h, LE i h ⊆ LF i h := fun i h =>
    Finset.image_subset_image ((C i).E_le_F h (x i))
  have hEm : ∀ i, Monotone (LE i) := fun i h h' hh =>
    Finset.image_subset_image ((C i).E_mono h h' (x i) hh)
  have hFm : ∀ i, Monotone (LF i) := fun i h h' hh =>
    Finset.image_subset_image ((C i).F_mono h h' (x i) hh)
  have hne : ∀ i h, (LE i h).Nonempty := fun i h =>
    ⟨_, Finset.mem_image_of_mem _ ((C i).E_self h (x i))⟩
  have hbad : ∀ i h, h ≤ J → ¬ (C i).PaperGood Δ (good i) h (x i) →
      v57Bad v57FloorLog LE LF X Y Δ (1/10) i h := by
    intro i h hh hg
    simp only [ModeComponents.PaperGood, not_and_or, not_le] at hg
    rcases hg with hsmall | htype | hfrac
    · exact Or.inl hsmall
    · exact Or.inr (Or.inl htype)
    · refine Or.inr (Or.inr ?_)
      change (1/10:ℝ) < (((X i ∪ Y i h) ∩ LF i h).card:ℝ)/(LF i h).card
      have hcover : (LF i h).filter (fun p => ¬ good i h p) ⊆ (X i ∪ Y i h) ∩ LF i h := by
        intro p hp
        obtain ⟨hpF,hpg⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_inter.mpr ⟨?_,hpF⟩
        by_cases he : nonexc i p
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpF,he,hpg⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hFm i hh hpF,he⟩)
      have hsplit := Finset.card_filter_add_card_filter_not (s := LF i h) (good i h)
      have hcnt := Finset.card_le_card hcover
      change 10*((LF i h).filter (good i h)).card < 9*(LF i h).card at hfrac
      have hpos : (0:ℝ) < (LF i h).card := by
        exact_mod_cast ((hne i h).mono (hEF i h)).card_pos
      have hr : (LF i h).card < 10*((X i ∪ Y i h) ∩ LF i h).card := by omega
      have hr' : ((LF i h).card:ℝ) < 10*(((X i ∪ Y i h) ∩ LF i h).card:ℝ) := by exact_mod_cast hr
      apply (lt_div_iff₀ hpos).mpr
      linarith
  apply v57_lemma86 N J Δ M A B δ (1/10) LE LF X Y hδ (by norm_num)
    hne hEF hlink hEm hFm hM
  · intro i p
    by_cases hp : nonexc i p
    · refine (Finset.card_le_card ?_).trans (hA i p hp)
      intro h hh
      obtain ⟨hh',hy⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨hh', (Finset.mem_filter.mp hy).2.2⟩
    · have he : ((Finset.range (J+1)).filter fun h => p ∈ Y i h) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro h hh
        exact hp (Finset.mem_filter.mp (Finset.mem_filter.mp hh).2).2.1
      rw [he, Finset.card_empty]; exact Nat.zero_le _
  · intro p
    refine (Finset.card_le_card ?_).trans (hB p)
    intro i hi
    obtain ⟨hi',hx⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi', (Finset.mem_filter.mp hx).2⟩
  · intro i hi
    have hs : δ*(J+1 : ℕ) < ((C i).paperBadHeights Δ (good i) J (x i)).card :=
      lt_of_not_ge (hside i hi)
    refine hs.trans_le ?_
    unfold ModeComponents.paperBadHeights
    rw [Finset.card_filter]; push_cast
    apply Finset.sum_le_sum
    intro h hh
    have hj : h ≤ J := by have := Finset.mem_range.mp hh; omega
    by_cases hg : (C i).PaperGood Δ (good i) h (x i)
    · simp [hg]; split_ifs <;> norm_num
    · simp [hg, hbad i h hj hg]
  · exact hbudget

end OpenAI086.ReferenceV71

namespace Auto.ModeSystem
open OpenAI086.ReferenceV71 OpenAI086.AdaptedV56
open scoped BigOperators
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

open Classical in
noncomputable def paperSideModes (b : ℤ) (J : ℤ × ℤ) :
    Finset (Ms.alive (ancAt Gd J (b - 4*S.K))) :=
  Finset.univ.filter fun x => ¬ (Ms.blockComps S hA b J).PaperCore SP.Δ
    (Ms.goodP S SP b) SP.Jst SP.δs x

open Classical in
noncomputable def paperSideEvents (b : ℤ) (J : ℤ × ℤ) : Finset (Finset Ms.Md) :=
  (Ms.paperSideModes S hA SP b J).image fun x =>
    ((Ms.blockComps S hA b J).E 0 x).map ⟨Subtype.val, Subtype.val_injective⟩

/-- Geometric chains of the *paper-side* events, with the actual exceptional
and height-bad predicates. The numerical height reserve remains explicit. -/
open Classical in
theorem paper_chain_events_bound (s : Finset Ms.Event)
    (hev : ∀ e ∈ s, e.2.2 ∈ Ms.paperSideEvents S hA SP e.1 e.2.1)
    (hdepth : ∀ e ∈ s, e.2.1.1 = e.1 - 2*S.K)
    (hsep : ∀ e ∈ s, ∀ e' ∈ s, e.1 < e'.1 → e.1 + 3*S.K ≤ e'.1)
    {M A B : ℕ} (hM : ∀ U : ℤ × ℤ, ((Ms.alive U).image Ms.keyOf).card ≤ M)
    (hB : ∀ (p : Ms.Key) (T : Finset ℤ), (∀ b ∈ T, ∃ e ∈ s, e.1 = b) →
      (T.filter fun b => ¬ Ms.nonexcAt S SP b p).card ≤ B)
    (hA' : ∀ b p, Ms.nonexcAt S SP b p →
      ((Finset.range (SP.Jst+1)).filter fun h => ¬ Ms.goodP S SP b h p).card ≤ A)
    (hδ : 0 < SP.δs)
    (hbudget : 2*((SP.Δ:ℝ)*(v57FloorLog M+1) + (A:ℝ)*(harmonic M:ℝ)/(1/10)) ≤
      SP.δs*(SP.Jst+1 : ℕ))
    {k : ℕ} {e : Ms.Event} (hc : LinkedChain (s : Set Ms.Event) (Ms.Linked S) k e) :
    ((k+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ)+(B:ℝ)*(harmonic M:ℝ)/(1/10))/SP.δs := by
  classical
  obtain ⟨c,hcs,hcR,-⟩ := hc
  set ev : ℕ → Ms.Event := fun i => c ⟨min i k, by omega⟩
  have hevs : ∀ i, ev i ∈ s := fun i => hcs _
  have hrep : ∀ i, ∃ x ∈ Ms.paperSideModes S hA SP (ev i).1 (ev i).2.1,
      ((Ms.blockComps S hA (ev i).1 (ev i).2.1).E 0 x).map
        ⟨Subtype.val, Subtype.val_injective⟩ = (ev i).2.2 := fun i =>
    Finset.mem_image.mp (hev _ (hevs i))
  choose x hxs hxE using hrep
  have hlinked : ∀ i, i < k → Ms.Linked S (ev i) (ev (i+1)) := by
    intro i hi
    have h1 : ev i = c (⟨i,hi⟩ : Fin k).castSucc := by
      simp only [ev]; congr 1; ext; simp [Nat.min_eq_left hi.le]
    have h2 : ev (i+1) = c (⟨i,hi⟩ : Fin k).succ := by
      simp only [ev]; congr 1; ext; simp [Nat.min_eq_left (Nat.succ_le_of_lt hi)]
    rw [h1,h2]; exact hcR ⟨i,hi⟩
  have hstrict : ∀ i j, i < j → j ≤ k → (ev i).1 < (ev j).1 := by
    intro i j hij hjk
    induction j, hij using Nat.le_induction with
    | base => exact (hlinked i (by omega)).2.1
    | succ j hij ih => exact (ih (by omega)).trans (hlinked j (by omega)).2.1
  have hinj : Set.InjOn (fun i => (ev i).1) (Finset.range (k+1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hstrict i j h (by omega)).ne hij
    · exact (hstrict j i h (by omega)).ne hij.symm
  apply paper_chain_bound k SP.Jst SP.Δ M A B
    (fun i => Ms.alive (ancAt Gd (ev i).2.1 ((ev i).1 - 4*S.K)))
    (fun i => Ms.blockComps S hA (ev i).1 (ev i).2.1) x
    (fun i => Ms.goodP S SP (ev i).1) (fun i => Ms.nonexcAt S SP (ev i).1) SP.δs hδ
  · intro i hi h
    obtain ⟨hsub,hlt,m,hm,m',hm',hmm⟩ := hlinked i hi
    rw [← hxE i] at hm
    rw [← hxE (i+1)] at hm'
    exact Ms.link_labels S hA (hdepth _ (hevs i)) (hdepth _ (hevs (i+1)))
      (hsep _ (hevs i) _ (hevs (i+1)) hlt) hsub (x i) (x (i+1)) hm hm' hmm h
  · intro i h
    refine (Finset.card_le_card ?_).trans (hM (ancAt Gd (ev i).2.1 ((ev i).1 - 4*S.K)))
    intro p hp
    obtain ⟨y,-,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨y.1,y.2,?_⟩
    unfold blockComps
    split <;> rfl
  · exact fun i p hp => hA' _ p hp
  · intro p
    refine le_trans ?_ (hB p ((Finset.range (k+1)).image fun i => (ev i).1) (by
      intro b hb
      obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hb
      exact ⟨ev i,hevs i,rfl⟩))
    rw [← Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hir,hne⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hir,hne⟩
  · intro i _
    simpa [paperSideModes] using hxs i
  · exact hbudget

end Auto.ModeSystem

#print axioms OpenAI086.ReferenceV71.paper_chain_bound
#print axioms Auto.ModeSystem.paper_chain_events_bound

namespace Auto.ModeSystem
open OpenAI086.AdaptedV56
open scoped BigOperators
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc)

/-- Reuse the actual schedule's exceptional-block and height-stabilization
bounds. The exact floor-log height reserve is deliberately explicit. -/
open Classical in
theorem paper_chain_length_schedule (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCA : 1 ≤ CA) (hδ : 0 < δs)
    (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (hQ : 1 ≤ S.Q0)
    (hW : 8 * ((S.dmax : ℝ) + 1)^3 * Real.log (2*S.H) / Real.log 2 ≤ W)
    (hdim : ∀ p, Ms.dvOf p + Ms.zc.dim ≤ S.dmax) {M : ℕ}
    (hM : ∀ U : ℤ × ℤ, ((Ms.alive U).image Ms.keyOf).card ≤ M)
    (R₀ : ℤ) (s : Finset Ms.Event)
    (hev : ∀ e ∈ s, e.2.2 ∈ Ms.paperSideEvents S (hV.six_le_A0 hCA hd2 hD hB)
      (S.sideParams δs) e.1 e.2.1)
    (hdepth : ∀ e ∈ s, e.2.1.1 = e.1 - 2*S.K)
    (hgrid : ∀ e ∈ s, (S.K : ℤ) ∣ e.1 - R₀)
    (hsep : ∀ e ∈ s, ∀ e' ∈ s, e.1 < e'.1 → e.1 + 3*S.K ≤ e'.1)
    (hbudget : 2*((((S.sideParams δs).Δ):ℝ)*(v57FloorLog M+1) +
      ((3*S.dmax*S.Rht : ℕ):ℝ)*(harmonic M:ℝ)/(1/10)) ≤
      (S.sideParams δs).δs*((S.sideParams δs).Jst+1 : ℕ))
    {k : ℕ} {e : Ms.Event} (hc : LinkedChain (s : Set Ms.Event) (Ms.Linked S) k e) :
    ((k+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ)+((4*S.dmax : ℕ):ℝ)*(harmonic M:ℝ)/(1/10))/
      (S.sideParams δs).δs := by
  have hA := hV.six_le_A0 hCA hd2 hD hB
  have hH2 := hV.two_le_H hd2 hD hB hQ
  have hAe : ∀ (p : Ms.Key) (T : Finset ℤ), (∀ b ∈ T, ∃ e ∈ s, e.1 = b) →
      (T.filter fun b => ¬ Ms.nonexcAt S (S.sideParams δs) b p).card ≤ 4 * S.dmax := by
    intro p T hT
    have hinj : Set.InjOn (fun b : ℤ => (b - R₀) / S.K)
        ((T.filter fun b => ¬ Ms.nonexcAt S (S.sideParams δs) b p : Finset ℤ) : Set ℤ) := by
      intro b hb b' hb' hbb
      obtain ⟨e, he, rfl⟩ := hT b (Finset.mem_filter.mp hb).1
      obtain ⟨e', he', rfl⟩ := hT b' (Finset.mem_filter.mp hb').1
      have h1 := Int.ediv_mul_cancel (hgrid e he)
      have h2 := Int.ediv_mul_cancel (hgrid e' he')
      have h3 : e.1 - R₀ = e'.1 - R₀ := by
        rw [← h1, ← h2]
        exact congrArg (· * (S.K : ℤ)) hbb
      linarith
    rw [← Finset.card_image_of_injOn hinj]
    have hdp := hdim p
    have hWd : 8 * (((Ms.dvOf p + Ms.zc.dim : ℕ) : ℝ) + 1) ^ 3 * Real.log (2 * S.H) /
        Real.log 2 ≤ W := by
      have hd' : ((Ms.dvOf p + Ms.zc.dim : ℕ) : ℝ) ≤ S.dmax := by exact_mod_cast hdp
      have hl : 0 ≤ Real.log (2 * S.H) / Real.log 2 :=
        div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
      have hc : (((Ms.dvOf p + Ms.zc.dim : ℕ) : ℝ) + 1) ^ 3 ≤ ((S.dmax : ℝ) + 1) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      refine le_trans ?_ hW
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) hl
    refine (S.exceptional_blocks_le hV hd2 hD hB hQ hWd
      (Fin.append (Ms.θvOf p) fun l => Ms.zc.θ l / S.Q0) Gd.baseLength_pos R₀ _ ?_).trans
      (by omega)
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hβ
    obtain ⟨hbT, hbne⟩ := Finset.mem_filter.mp hb
    obtain ⟨e, he, rfl⟩ := hT b hbT
    have h1 := Int.ediv_mul_cancel (hgrid e he)
    have h2 : R₀ + (e.1 - R₀) / (S.K : ℤ) * (S.K : ℤ) = e.1 := by rw [h1]; ring
    rw [h2]
    exact Ms.exceptionalAt_of_not_nonexcAt S δs (by linarith) hbne
  -- the height-bad incidences of a nonexceptional key at one event (lem:stabilize)
  have hAh : ∀ (b : ℤ) (p : Ms.Key), Ms.nonexcAt S (S.sideParams δs) b p →
      ((Finset.range ((S.sideParams δs).Jst + 1)).filter fun h =>
        ¬ Ms.goodP S (S.sideParams δs) b h p).card ≤ 3 * S.dmax * S.Rht := fun b p hp =>
    hV.stabGood_bad_card hCA hd2 hD hB Ms.dvOf
      (fun k => Fin.append (Ms.θvOf k) fun l => Ms.zc.θ l / S.Q0) Gd.baseLength b p (hdim p)
      (Ms.not_exceptionalAt_of_nonexcAt S δs hp) (S.Jstar + 1)
  exact Ms.paper_chain_events_bound S hA (S.sideParams δs) s hev hdepth hsep hM hAe hAh
    (by simpa [ModeSchedule.sideParams] using hδ) hbudget hc

end Auto.ModeSystem
#print axioms Auto.ModeSystem.paper_chain_length_schedule

namespace OpenAI086.ReferenceV71
open Auto OpenAI086.AdaptedV56

/-- The base 1.1 rank has at most eleven levels per natural logarithmic
unit. This is the extra quantitative factor needed for the exact density
argument, rather than the reference ratio-density argument. -/
theorem rank_le_eleven_log {M : ℕ} (hM : 1 ≤ M) :
    (v57FloorLog M : ℝ) ≤ 11 * Real.log M := by
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hl : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg hM1
  have hb : (1/11:ℝ) ≤ Real.log (11/10:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 10/11 by norm_num)
    rw [show (10/11:ℝ) = (11/10:ℝ)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hb0 : 0 < Real.log (11/10:ℝ) := by linarith
  have hf : (v57FloorLog M:ℝ) ≤ Real.log M / Real.log (11/10:ℝ) :=
    Nat.floor_le (div_nonneg hl hb0.le)
  refine hf.trans ?_
  apply (div_le_iff₀ hb0).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hb hl]

/-- The precise reserve required by Lemma 8.6 is automatic for the
reference schedule once its height coefficient is at least 340. The
bound uses the actual floor-log and harmonic terms, not a ratio proxy. -/
theorem paper_height_reserve (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCj : 340 ≤ Cj)
    (hδ : 0 < δs) (hδ1 : δs ≤ 1) (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar)
    (hDm : 2 ≤ S.Dm) {M : ℕ} (hM1 : 1 ≤ M) (hMD : (M:ℝ) ≤ 2*S.Dm) :
    2*((((S.sideParams δs).Δ):ℝ)*(v57FloorLog M+1) +
      ((3*S.dmax*S.Rht : ℕ):ℝ)*(harmonic M:ℝ)/(1/10)) ≤
      (S.sideParams δs).δs*((S.sideParams δs).Jst+1 : ℕ) := by
  have hR := hV.thirty_le_Rht hd2 hD
  have hL : Real.log (M:ℝ) ≤ Real.log (2*S.Dm) :=
    Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) hMD
  have hL1 : 1 ≤ Real.log (2*S.Dm) := by
    have h4 : Real.log 4 ≤ Real.log (2*S.Dm) := Real.log_le_log (by norm_num) (by linarith)
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  have hd2' : (2:ℝ) ≤ S.dmax := by exact_mod_cast hd2
  have hR' : (30:ℝ) ≤ S.Rht := by exact_mod_cast hR
  let X : ℝ := (S.dmax:ℝ)*S.Rht
  let L : ℝ := Real.log (2*S.Dm)
  have hX : 60 ≤ X := by dsimp [X]; nlinarith only [hd2',hR']
  have hXL : 0 ≤ X*L := mul_nonneg (by linarith [hX]) (by change 0 ≤ Real.log (2*S.Dm); linarith)
  have hrank : (v57FloorLog M:ℝ) ≤ 11*L := by
    exact (rank_le_eleven_log hM1).trans (mul_le_mul_of_nonneg_left hL (by norm_num))
  have hharm : (harmonic M:ℝ) ≤ 2*L := by
    have h := harmonic_le_one_add_log M
    dsimp [L] at *
    linarith
  have hleft : 2*(10*((v57FloorLog M:ℝ)+1) + (3*X)*(harmonic M:ℝ)/(1/10)) ≤ 340*(X*L) := by
    have hL' : 1 ≤ L := hL1
    have hmul := mul_le_mul_of_nonneg_left hharm (show 0 ≤ X by linarith)
    have hXL' := mul_le_mul_of_nonneg_right hX (show 0 ≤ L by linarith)
    nlinarith only [hrank,hL',hmul,hXL']
  have hJs := hV.Jstar_ge
  have hCj' : (340:ℝ) ≤ Cj := by exact_mod_cast hCj
  have hδi : 1 ≤ δs⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have he : δs*(Cj*δs⁻¹^2*S.dmax*S.Rht*L) = Cj*δs⁻¹*(X*L) := by
    simp only [X]; field_simp
  have hright : 340*(X*L) ≤ δs*S.Jstar := by
    calc
      _ ≤ Cj*δs⁻¹*(X*L) := by
        refine mul_le_mul_of_nonneg_right ?_ hXL
        nlinarith only [hCj',hδi]
      _ = δs*(Cj*δs⁻¹^2*S.dmax*S.Rht*L) := he.symm
      _ ≤ δs*S.Jstar := mul_le_mul_of_nonneg_left hJs hδ.le
  have hΔ : ((S.sideParams δs).Δ:ℝ) = 10 := by norm_num [ModeSchedule.sideParams]
  have hJ : ((S.sideParams δs).Jst:ℝ) = S.Jstar := rfl
  have hδ' : (S.sideParams δs).δs = δs := rfl
  rw [hΔ,hδ']; push_cast
  rw [hJ]
  have h := hleft.trans hright
  dsimp [X] at h
  linarith

end OpenAI086.ReferenceV71
#print axioms OpenAI086.ReferenceV71.rank_le_eleven_log
#print axioms OpenAI086.ReferenceV71.paper_height_reserve

namespace Auto.ModeSystem
open OpenAI086.AdaptedV56 OpenAI086.ReferenceV71
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc)

/-- The actual scheduled linked-chain estimate, without an additional
height-reserve assumption. The remaining event-class and path-label
hypotheses are geometric data, as in the reference schedule. -/
open Classical in
theorem paper_chain_length_valid (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCA : 1 ≤ CA) (hCj : 340 ≤ Cj)
    (hδ : 0 < δs) (hδ1 : δs ≤ 1)
    (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (hQ : 1 ≤ S.Q0)
    (hDm : 2 ≤ S.Dm) (hW : 8 * ((S.dmax : ℝ) + 1)^3 * Real.log (2*S.H) / Real.log 2 ≤ W)
    (hdim : ∀ p, Ms.dvOf p + Ms.zc.dim ≤ S.dmax) {M : ℕ}
    (hM1 : 1 ≤ M) (hMD : (M:ℝ) ≤ 2*S.Dm)
    (hM : ∀ U : ℤ × ℤ, ((Ms.alive U).image Ms.keyOf).card ≤ M)
    (R₀ : ℤ) (s : Finset Ms.Event)
    (hev : ∀ e ∈ s, e.2.2 ∈ Ms.paperSideEvents S (hV.six_le_A0 hCA hd2 hD hB)
      (S.sideParams δs) e.1 e.2.1)
    (hdepth : ∀ e ∈ s, e.2.1.1 = e.1 - 2*S.K)
    (hgrid : ∀ e ∈ s, (S.K : ℤ) ∣ e.1 - R₀)
    (hsep : ∀ e ∈ s, ∀ e' ∈ s, e.1 < e'.1 → e.1 + 3*S.K ≤ e'.1)
    {k : ℕ} {e : Ms.Event} (hc : LinkedChain (s : Set Ms.Event) (Ms.Linked S) k e) :
    ((k+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ)+((4*S.dmax : ℕ):ℝ)*(harmonic M:ℝ)/(1/10))/
      (S.sideParams δs).δs := by
  exact Ms.paper_chain_length_schedule S hV hCA hδ hd2 hD hB hQ hW hdim hM R₀ s hev
    hdepth hgrid hsep (paper_height_reserve S hV hCj hδ hδ1 hd2 hD hDm hM1 hMD) hc

end Auto.ModeSystem
#print axioms Auto.ModeSystem.paper_chain_length_valid
