import Mathlib
import OpenAI086.FiniteDyadicOrderedWidthExpansion

/-!
# V17: flattening ordered width sums into an explicit tuple list

`finiteExpandedLinearProductOnWidths` is a recursively nested sum.
For the second half of the proof of Lemma 3.3 we need one finite list
of tuples of widths, so that the masked tuple-Bessel theorem can be
applied to the SAME set of levels for every row.

Here `enumerateWidthTuples widths m` is a concrete list of all words of
length `m` in the finite width alphabet. The operator identities below
preserve multiplication order, including for noncommuting projections.
This does not itself apply the row-Bessel theorem to those tuples.
-/

namespace OpenAI086

/-- Enumerate width tuples, one choice per layer of a product. -/
def enumerateWidthTuples (widths : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => widths.flatMap
      (fun w => (enumerateWidthTuples widths n).map (List.cons w))

/-- Ordered product associated with one chosen width tuple. The
first layer is applied first; the remaining layers compose on its
left. Ill-formed length mismatches are assigned the zero operator. -/
def finiteWordBlockProduct {d : ℕ} {Layer : Type*}
    (Q : Layer → ℕ → FiniteRealEnd d) :
    List Layer → List ℕ → FiniteRealEnd d
  | [], [] => LinearMap.id
  | i :: rest, w :: tail =>
      (finiteWordBlockProduct Q rest tail).comp (Q i w)
  | _, _ => 0

/-- Nested list-width sum, with the same operator order as the original
prefix product. It is extensionally equal to the sum over all words. -/
def finiteListWidthExpandedProduct {d : ℕ} {Layer : Type*}
    (widths : List ℕ) (Q : Layer → ℕ → FiniteRealEnd d) :
    List Layer → FiniteRealEnd d
  | [] => LinearMap.id
  | i :: rest =>
      (widths.map (fun w =>
        (finiteListWidthExpandedProduct widths Q rest).comp (Q i w))).sum

private theorem sum_flatmap_double {A B C : Type*}
    [AddCommMonoid C] (xs : List A) (ys : List B) (f : A → B → C) :
    ((xs.flatMap (fun a => ys.map (f a))).sum) =
      (xs.map (fun a => (ys.map (f a)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      simp [List.flatMap_cons, List.sum_append, ih]

private theorem linear_map_list_sum_comp {d : ℕ}
    (xs : List (FiniteRealEnd d)) (F : FiniteRealEnd d) :
    xs.sum.comp F = (xs.map (fun G => G.comp F)).sum := by
  induction xs with
  | nil =>
      apply LinearMap.ext
      intro x
      simp
  | cons G rest ih =>
      apply LinearMap.ext
      intro x
      have h := congrArg (fun H : FiniteRealEnd d => H x) ih
      simp only [List.sum_cons, LinearMap.comp_apply,
        LinearMap.add_apply, List.map_cons] at *
      rw [h]

/-- Flatten ALL nested width choices into a single finite list of width
words. No commutation or projection assumptions are used. -/
theorem finite_list_width_product_as_tuple_sum {d : ℕ}
    {Layer : Type*} (widths : List ℕ)
    (Q : Layer → ℕ → FiniteRealEnd d) :
    ∀ layers : List Layer,
      finiteListWidthExpandedProduct widths Q layers =
        ((enumerateWidthTuples widths layers.length).map
          (finiteWordBlockProduct Q layers)).sum := by
  intro layers
  induction layers with
  | nil => simp [finiteListWidthExpandedProduct,
        enumerateWidthTuples, finiteWordBlockProduct]
  | cons i rest ih =>
      have hlocal (w : ℕ) :
          ((enumerateWidthTuples widths rest.length).map
            (fun tail => finiteWordBlockProduct Q (i :: rest)
              (w :: tail))).sum =
          (finiteListWidthExpandedProduct widths Q rest).comp (Q i w) := by
        have hcomp := linear_map_list_sum_comp
          ((enumerateWidthTuples widths rest.length).map
            (finiteWordBlockProduct Q rest)) (Q i w)
        rw [← ih]
        simpa only [List.map_map, Function.comp_def,
          finiteWordBlockProduct] using hcomp.symm
      have hflat := sum_flatmap_double widths
        (enumerateWidthTuples widths rest.length)
        (fun w tail => finiteWordBlockProduct Q (i :: rest) (w :: tail))
      simp only [finiteListWidthExpandedProduct, List.length_cons,
        enumerateWidthTuples, List.map_flatMap] at *
      rw [hflat]
      congr 1
      apply List.map_congr_left
      intro w hw
      exact (hlocal w).symm

end OpenAI086
