import TrilinearHT.Auto.Sec14_5bExportedSideEstimate

/-! Lemma 7.3: summation for a supplied coloring into disjoint depth-interval
families, on the reference's actual certified-cell variation capacity.
No assertion that an arbitrary bounded-overlap family is already colored. -/
namespace OpenAI086.ReferenceV67
open Auto MeasureTheory
open scoped Classical BigOperators

theorem variation_colored {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)
    {γ V : Type*} [Fintype V] (Gs : Finset γ) (Z : γ → ℤ → ColumnL2 V)
    (ok : γ → ℤ × ℤ → Prop) {B : ℝ} (hB : A.VarCap Gs Z ok B)
    (m : ℕ) {ι : Type} [Fintype ι] (r t : Fin m → ι → ℕ)
    (hrt : ∀ c i, r c i ≤ t c i)
    (hdis : ∀ c i i', i ≠ i' → Disjoint (Finset.Ioc (r c i) (t c i)) (Finset.Ioc (r c i') (t c i')))
    (htd : ∀ c i, t c i ≤ A.treeDepth) (Ec : Fin m → γ → ι → Finset (ℤ × ℤ))
    (hEc : ∀ c g i, ∀ J ∈ Ec c g i, J ∈ A.cells ∧ J.1 = A.R.1 + t c i ∧ ok g J) :
    ∑ c : Fin m, ∑ g ∈ Gs, ∑ i, ‖columnL2Restriction
      (⋃ J ∈ Ec c g i, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (Z g (A.R.1 + t c i) - Z g (A.R.1 + r c i))‖ ^ 2 ≤ (m : ℝ) * B := by
  classical
  calc _ ≤ ∑ _c : Fin m, B := Finset.sum_le_sum fun c _ => hB (r c) (t c) (hrt c) (hdis c) (htd c) (Ec c) (hEc c)
    _ = _ := by simp

end OpenAI086.ReferenceV67
#print axioms OpenAI086.ReferenceV67.variation_colored
