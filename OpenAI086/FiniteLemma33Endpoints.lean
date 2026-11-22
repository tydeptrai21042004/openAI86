import Mathlib
import OpenAI086.FiniteLemma33Target
import OpenAI086.GeneralNestedProjectionEnergy

/-!
# Closed endpoint cases of the actual finite-real Lemma 3.3 goal

The V6 finite targets were previously definitions of open propositions.
This module proves the zero-layer row statement and the zero/one-layer
square-variation statements with precisely the same target definitions.
It also gives the sharp row estimate for any number of noncommuting
projection layers when all rows choose the SAME prefix index.

The variable-index row bound for m >= 1 and the square variation for
m >= 2 are not derived here; nor is the arbitrary complex Hilbert version.
-/

namespace OpenAI086

/-- With no projection layers, all row prefixes are the input itself. -/
theorem finite_lemma33_row_prefix_zero
    {d : ℕ} (T rows : ℕ)
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (B : Fin rows → (Fin d → ℝ) → ℝ)
    (choice : Fin rows → Fin (T + 1)) :
    finiteLemma33RowPrefixGoal 0 T rows P B choice := by
  unfold finiteLemma33RowPrefixGoal
  intro _ hrow x
  simpa [finiteSequentialProjectionProduct] using hrow x

/-- With no projection layers, the product is the identity at all levels,
so its variation is zero. -/
theorem finite_lemma33_variation_zero
    {d : ℕ} (T : ℕ)
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ)) :
    finiteLemma33VariationGoal 0 T P := by
  unfold finiteLemma33VariationGoal
  intro _ x
  simp [finiteSequentialProjectionProduct, finiteRealPair]

/-- The exact m = 1 square-variation estimate is already present in
GeneralNestedProjectionEnergy.  Here it is proved for the *same typed
formula* as the full finite Lemma 3.3 target, rather than a proxy model. -/
theorem finite_lemma33_variation_one
    {d : ℕ} (T : ℕ)
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ)) :
    finiteLemma33VariationGoal 1 T P := by
  unfold finiteLemma33VariationGoal
  intro hsys x
  obtain ⟨hsym, hidemp, hnested⟩ := hsys 0 (by omega)
  have h := nested_projection_square_variation_bound
    (P 0) hsym hidemp hnested x T
  simpa [finiteSequentialProjectionProduct] using h

/-- General ordered projection chains are contractions.  The order of
the listed layers is preserved, without commutativity assumptions. -/
theorem finite_projection_foldl_energy
    {d : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (layers : List ℕ) (k : ℕ) (x : Fin d → ℝ) :
    finiteRealPair (layers.foldl (fun z i => P i k z) x)
      (layers.foldl (fun z i => P i k z) x) ≤ finiteRealPair x x := by
  induction layers generalizing x with
  | nil => exact le_rfl
  | cons i rest ih =>
      change finiteRealPair
        (rest.foldl (fun z j => P j k z) (P i k x))
        (rest.foldl (fun z j => P j k z) (P i k x)) ≤
        finiteRealPair x x
      exact (ih (P i k x)).trans
        (nested_projection_single_energy (P i) (hsym i) (hidemp i) k x)

/-- Sharp row-Bessel estimate at a common depth for any number of
noncommuting orthogonal projection layers.  This is weaker than the
row-adaptive prefix theorem, where each row chooses its own depth. -/
theorem finite_common_prefix_noncommuting_row_bessel
    {d rows : ℕ}
    (P : ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ))
    (hsym : ∀ i k u v,
      finiteRealPair (P i k u) v = finiteRealPair u (P i k v))
    (hidemp : ∀ i k u, P i k (P i k u) = P i k u)
    (B : Fin rows → (Fin d → ℝ) → ℝ)
    (hrow : ∀ y : Fin d → ℝ,
      (∑ r : Fin rows, (B r y) ^ 2) ≤ finiteRealPair y y)
    (m k : ℕ) (x : Fin d → ℝ) :
    (∑ r : Fin rows,
      (B r (finiteSequentialProjectionProduct P m k x)) ^ 2) ≤
      finiteRealPair x x := by
  calc
    (∑ r : Fin rows,
      (B r (finiteSequentialProjectionProduct P m k x)) ^ 2) ≤
        finiteRealPair (finiteSequentialProjectionProduct P m k x)
          (finiteSequentialProjectionProduct P m k x) :=
        hrow (finiteSequentialProjectionProduct P m k x)
    _ ≤ finiteRealPair x x := by
      exact finite_projection_foldl_energy P hsym hidemp (List.range m) k x

end OpenAI086
