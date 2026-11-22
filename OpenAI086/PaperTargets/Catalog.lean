import Mathlib

/-!
# 59-item paper audit in Lean

The result identifiers and source-statement openings below are **metadata**,
not proofs. For 42 previously open results, a separate finite proxy model
now exists, explicitly marked as NOT the original paper statement.
-/

namespace OpenAI086.PaperTargets

inductive PaperResult where
  | result_1_1
  | result_2_1
  | result_2_2
  | result_2_3
  | result_2_4
  | result_3_1
  | result_3_2
  | result_3_3
  | result_3_4
  | result_3_5
  | result_4_1
  | result_4_2
  | result_4_3
  | result_4_4
  | result_4_5
  | result_4_6
  | result_4_7
  | result_4_8
  | result_4_9
  | result_4_10
  | result_4_11
  | result_4_12
  | result_5_1
  | result_5_2
  | result_5_3
  | result_5_4
  | result_5_5
  | result_5_6
  | result_5_7
  | result_5_8
  | result_6_1
  | result_6_2
  | result_6_3
  | result_6_4
  | result_6_5
  | result_6_6
  | result_6_7
  | result_6_8
  | result_6_9
  | result_7_1
  | result_7_2
  | result_7_3
  | result_7_4
  | result_7_5
  | result_8_1
  | result_8_2
  | result_8_3
  | result_8_4
  | result_8_5
  | result_8_6
  | result_8_7
  | result_8_8
  | result_8_9
  | result_8_10
  | result_8_11
  | result_8_12
  | result_9_1
  | result_9_2
  | result_9_3
  deriving DecidableEq, Repr, Inhabited

def allPaperResults : List PaperResult := [
  .result_1_1,
  .result_2_1,
  .result_2_2,
  .result_2_3,
  .result_2_4,
  .result_3_1,
  .result_3_2,
  .result_3_3,
  .result_3_4,
  .result_3_5,
  .result_4_1,
  .result_4_2,
  .result_4_3,
  .result_4_4,
  .result_4_5,
  .result_4_6,
  .result_4_7,
  .result_4_8,
  .result_4_9,
  .result_4_10,
  .result_4_11,
  .result_4_12,
  .result_5_1,
  .result_5_2,
  .result_5_3,
  .result_5_4,
  .result_5_5,
  .result_5_6,
  .result_5_7,
  .result_5_8,
  .result_6_1,
  .result_6_2,
  .result_6_3,
  .result_6_4,
  .result_6_5,
  .result_6_6,
  .result_6_7,
  .result_6_8,
  .result_6_9,
  .result_7_1,
  .result_7_2,
  .result_7_3,
  .result_7_4,
  .result_7_5,
  .result_8_1,
  .result_8_2,
  .result_8_3,
  .result_8_4,
  .result_8_5,
  .result_8_6,
  .result_8_7,
  .result_8_8,
  .result_8_9,
  .result_8_10,
  .result_8_11,
  .result_8_12,
  .result_9_1,
  .result_9_2,
  .result_9_3
]

def originalPdfPage : PaperResult → ℕ
  | .result_1_1 => 2
  | .result_2_1 => 4
  | .result_2_2 => 4
  | .result_2_3 => 4
  | .result_2_4 => 5
  | .result_3_1 => 7
  | .result_3_2 => 8
  | .result_3_3 => 8
  | .result_3_4 => 9
  | .result_3_5 => 13
  | .result_4_1 => 15
  | .result_4_2 => 15
  | .result_4_3 => 16
  | .result_4_4 => 18
  | .result_4_5 => 20
  | .result_4_6 => 21
  | .result_4_7 => 22
  | .result_4_8 => 22
  | .result_4_9 => 23
  | .result_4_10 => 26
  | .result_4_11 => 27
  | .result_4_12 => 27
  | .result_5_1 => 30
  | .result_5_2 => 31
  | .result_5_3 => 32
  | .result_5_4 => 33
  | .result_5_5 => 34
  | .result_5_6 => 35
  | .result_5_7 => 37
  | .result_5_8 => 38
  | .result_6_1 => 40
  | .result_6_2 => 41
  | .result_6_3 => 42
  | .result_6_4 => 43
  | .result_6_5 => 45
  | .result_6_6 => 46
  | .result_6_7 => 48
  | .result_6_8 => 49
  | .result_6_9 => 50
  | .result_7_1 => 52
  | .result_7_2 => 53
  | .result_7_3 => 58
  | .result_7_4 => 60
  | .result_7_5 => 62
  | .result_8_1 => 65
  | .result_8_2 => 67
  | .result_8_3 => 68
  | .result_8_4 => 69
  | .result_8_5 => 69
  | .result_8_6 => 70
  | .result_8_7 => 70
  | .result_8_8 => 71
  | .result_8_9 => 72
  | .result_8_10 => 74
  | .result_8_11 => 75
  | .result_8_12 => 76
  | .result_9_1 => 81
  | .result_9_2 => 87
  | .result_9_3 => 89

def paperItemDescription : PaperResult → String
  | .result_1_1 => "Theorem 1.1: Theorem 1.1. There is a finite constant C such that ∥T(f1, f2, f3)∥L1(R) ≤C"
  | .result_2_1 => "Lemma 2.1: Lemma 2.1 (Local absolute estimate). If pj ≥1 and P3 j=0 p−1"
  | .result_2_2 => "Theorem 2.2: Theorem 2.2 (Uniform local estimate). For some q ∈(2, 3), the constants CN(q) are bounded independently of N."
  | .result_2_3 => "Proposition 2.3: Proposition 2.3 (Normalized absorption estimate). For a suitable fixed q ∈(2, 3) and every sufficiently small fixed c > 0, there is an A < ∞, independent of N, with the following property."
  | .result_2_4 => "Lemma 2.4: Lemma 2.4 (Outer reduction). Proposition 2.3 implies Theorem 2.2, and Theorem 2.2 implies Theorem 1.1."
  | .result_3_1 => "Lemma 3.1: Lemma 3.1 (Packing of attempts). Suppose a construction on a root J sends exceptional cells and all their descendants to new estimates on disjoint subroots. Suppose that, at every root R, the"
  | .result_3_2 => "Lemma 3.2: Lemma 3.2 (Coefficient and projection bounds). If A is any set of columns available on a cell I, then"
  | .result_3_3 => "Lemma 3.3: Lemma 3.3 (Products of nested prefixes). Let X be a Hilbert space, and for 1 ≤i ≤m let P i"
  | .result_3_4 => "Lemma 3.4: Lemma 3.4 (Compression). Use the column system and budget D ≥2 above on a finite dyadic tree with root J. Let P 1, . . . , P m be inherited mask families, with their local orthogonal projections."
  | .result_3_5 => "Lemma 3.5: Lemma 3.5 (Height bins). Let d ≥1, B ≥2, and ξ ∈Rd. Let E ="
  | .result_4_1 => "Definition 4.1: Definition 4.1 (Quadratic chart atom). A quadratic chart atom is a function φ(y) = e(λy2 + βy)"
  | .result_4_2 => "Lemma 4.2: Lemma 4.2 (Elementary chart operations). Complex conjugation, a product of a bounded number of atoms, and translation or affine rescaling of the real argument preserve the class (1), with a"
  | .result_4_3 => "Lemma 4.3: Lemma 4.3 (Scale-wise Weyl alternative). Let ϑ be supported in a fixed box in Rk, with supremum norm and Lipschitz norm at most H. Suppose 0 < δ < 1/2 and"
  | .result_4_4 => "Lemma 4.4: Lemma 4.4 (Chart expansion and uniform tails). Suppose a rational orthogonal splitting satisfies (2), with heights and the indicated sizes at most B. On a fixed box in Rk there is an exact absolutely"
  | .result_4_5 => "Lemma 4.5: Lemma 4.5 (Progression separation). Let φi, φk be bounded atoms of complexity at most H in two distinct slots i, k, and let a, b denote the remaining slots. Their product has an exact absolutely"
  | .result_4_6 => "Lemma 4.6: Lemma 4.6 (Single-scale separation). Fix a term in (4), without its coefficient, of complexity at most H. Let ζ be a fixed nonnegative smooth function, equal to one on the range of t/r allowed by"
  | .result_4_7 => "Theorem 4.7: Theorem 4.7 (Leng–Sah–Sawhney). For a 1-bounded function f : [L] →C with ∥f∥U3[L] ≥δ, there are a degree-two filtered nilmanifold G/Γ, a polynomial sequence g : Z →G adapted to its"
  | .result_4_8 => "Lemma 4.8: Lemma 4.8 (Elementary cube bounds). The quantity ∥· ∥U is a seminorm. The mixed cube form with possibly different functions gω at its eight vertices satisfies"
  | .result_4_9 => "Lemma 4.9: Lemma 4.9 (Continuous bounded inverse). For 0 < δ < 1/2, let g be supported on an interval I, with ∥g∥∞≤1 and ∥g∥U(I) ≥δ. There is a bounded atom φ of complexity at most"
  | .result_4_10 => "Lemma 4.10: Lemma 4.10 (Structured, uniform, and L1 decomposition). For 0 < τ < 1/2 and a function f on I with ∥f∥∞≤1, there is a finite decomposition"
  | .result_4_11 => "Lemma 4.11: Lemma 4.11 (A generalized von Neumann bound with one L2 input). For four distinct slots occupied by R, g, b, c, one has"
  | .result_4_12 => "Lemma 4.12: Lemma 4.12 (Local detection). Fix q > 2 and C1 ≥1. Suppose that R, h, u, v occupy the four slots in any order and satisfy"
  | .result_5_1 => "Lemma 5.1: Lemma 5.1 (A scale sum for one separated term). Suppose the inputs in positions a, b are admissible sequences associated with Fa, Fb, with parameters Dh, L. For m ≥0, let Im consist of"
  | .result_5_2 => "Corollary 5.2: Corollary 5.2 (A finite predictor list). Fix the two low atoms on J, with complexity at most Hlow. For every B ≥1, their product in the form can be replaced, with absolute length-weighted scale-sum"
  | .result_5_3 => "Lemma 5.3: Lemma 5.3 (Delayed predictor replacement). Consider one fixed term of (6), born on J. Suppose the nested predictor family in position a contains Φp on every use interval and on all its descendants."
  | .result_5_4 => "Lemma 5.4: Lemma 5.4 (Inherited adaptive approximation). Suppose ∥fj∥q,I ≤1 throughout a finite normalized subtree. For every sufficiently large k, one can construct, on segments whose roots have bounded"
  | .result_5_5 => "Lemma 5.5: Lemma 5.5 (The two-earliest-increments expansion). Take the two earliest increment levels u < t in distinct positions i, j, and let a, b be the complementary positions. Define"
  | .result_5_6 => "Proposition 5.6: Proposition 5.6 (Truncating the two high positions). For the tuple above, put k = kt. There are an integer K0 ≤kO(1), further bounded-packing segments, and nested projection families P new"
  | .result_5_7 => "Lemma 5.7: Lemma 5.7 (Few active scales for a fixed triple). Fix three bounded basic scalar columns, in three distinct positions, on their common birth subtree. For a dyadic interval I let AI be the norm of"
  | .result_5_8 => "Proposition 5.8: Proposition 5.8 (Reduction to the active cell minimum). The remaining patterns, with at least three B arguments and optionally one U argument, can be restricted, with total absolute error at"
  | .result_6_1 => "Lemma 6.1: Lemma 6.1 (Separation of different tags). Fix an upper bound exp(kO(1)) for the complexities of the single columns under consideration. Given τ2 > 0 with log(1/τ2) ≤kO(1), one can choose"
  | .result_6_2 => "Lemma 6.2: Lemma 6.2 (Endpoint bounds along a short path). Suppose two tags can be joined, at one scale, by a path of length L ≤poly(P, k). Their difference data satisfy (2) in their own endpoint coordinates,"
  | .result_6_3 => "Lemma 6.3: Lemma 6.3 (Color budget and exceptional roots). For sufficiently large starting k, the preceding construction uses at most L colors, with at most d8"
  | .result_6_4 => "Lemma 6.4: Lemma 6.4 (Mask inclusion, closure, and separation). The following assertions hold for every allowed pad."
  | .result_6_5 => "Lemma 6.5: Lemma 6.5 (Bessel separation of usable endpoint spaces). Fix a slot and a color. For each of finitely many groups G let ZG be a finite sum of available main pure columns, with constant"
  | .result_6_6 => "Lemma 6.6: Lemma 6.6 (A uniform same-tag test). For each original vertex v there is a fixed template family in every slot, consisting of bounded pure columns of normalized tag v and unrestricted linear"
  | .result_6_7 => "Lemma 6.7: Lemma 6.7 (Catalog closure and its budget). The main closure and then the helper closure can be performed at every active cell with path counts satisfying log nmax ≤kO(1). The exponent is fixed"
  | .result_6_8 => "Proposition 6.8: Proposition 6.8 (Localization into current groups). For an active pattern in (11), there are poly(k) fixed search leaves such that, up to total absolute length-weighted error at most Ce−k|R|,"
  | .result_6_9 => "Lemma 6.9: Lemma 6.9 (Outgoing filters and near-band defects). At a use of (14), suppose slots a, b are fixed side states Sa, Sb, chosen independently of the helper catalog. Suppose the other two slots have"
  | .result_7_1 => "Lemma 7.1: Lemma 7.1. Let (X, µ) and (W, ν) be finite measure spaces. If 1 < r, s, t < ∞and v ∈Ar(R), then"
  | .result_7_2 => "Lemma 7.2: Lemma 7.2 (Short-block comparison). Let 2 < q < 3. Let T be a finite dyadic tree piece with root R, whose internal summation intervals belong to at most K consecutive depths and to the original"
  | .result_7_3 => "Lemma 7.3: Lemma 7.3 (Variation on certified endpoint cells). Let ZG,s be a basic coarse output in Equa- tion (14). Consider a common collection of disjoint, or boundedly overlapping, depth intervals [r, t]."
  | .result_7_4 => "Lemma 7.4: Lemma 7.4 (Side stacks). Fix a near offset q −p in Equation (15), a transfer step, and a search path. The two time-dependent side inputs can be written, at their uses, as a sum of at most"
  | .result_7_5 => "Proposition 7.5: Proposition 7.5 (Side estimate). Assume the base and localization hypotheses above, the helper conclusions of Lemma 6.9, and the linear-side square bound (17). Fix p ∈(2/3, 1). After common"
  | .result_8_1 => "Lemma 8.1: Lemma 8.1 (First-match expansion and bounded lift). At each first match I0, there is a finite, permanently labeled expansion"
  | .result_8_2 => "Lemma 8.2: Lemma 8.2 (Exceptional blocks and the tiny rational space). Each primary is exceptional in at most Cdmax blocks on a path. At a nonexceptional block, let Krat be the rational span of all"
  | .result_8_3 => "Lemma 8.3: Lemma 8.3 (Height stabilization). For a nonexceptional primary, all but CdmaxRht ∗heights have"
  | .result_8_4 => "Lemma 8.4: Lemma 8.4 (Coherence of good predicates). Good modes in one CURRENT component at height h have the same PRE component at height h −∆. The core/side decision is constant on each"
  | .result_8_5 => "Lemma 8.5: Lemma 8.5 (Entry-rank summation). Let S1 ⊆· · · ⊆ST be nonempty finite sets with |ST | ≤M. Suppose Xt ⊆St, and each element belongs to at most A of the sets Xt. Then"
  | .result_8_6 => "Lemma 8.6: Lemma 8.6 (Bad-density chains). Fix 0 < δ, β < 1, integers J ≥∆≥1, and M ≥1. For 1 ≤i ≤N, 0 ≤h ≤J, let Pi,h and Ci,h be nonempty sets of primary labels, each increasing in h,"
  | .result_8_7 => "Lemma 8.7: Lemma 8.7 (Separated mode rows). Fix a role and group. Consider a family of dyadic cells Je, with a nonempty set Me of available mode labels on each cell. Suppose that along every path:"
  | .result_8_8 => "Lemma 8.8: Lemma 8.8 (Composition with the lift and main histories). Fix a role. For each group, suppose a family of mode projection rows Pe, supported on cells Je, has squared Bessel bound at most G0."
  | .result_8_9 => "Proposition 8.9: Proposition 8.9 (Square energy of the linear side). For each basic-B role, on every retained vb-cell let Vl,G,b be the exact subtotal of the linear-side modes in eZl,G,b, including their private"
  | .result_8_10 => "Lemma 8.10: Lemma 8.10 (Hereditary representatives). Fix the height, role, group, and type. We can choose a representative mode a ∈Eh−∆for every successful component so that it is inherited whenever an"
  | .result_8_11 => "Lemma 8.11: Lemma 8.11 (Component-size comparison). At every actual cell, σ2"
  | .result_8_12 => "Proposition 8.12: Proposition 8.12 (Top count). After removing summands on first stopping cells of arbitrarily small fixed total relative length, the following holds on every retained path. Fix a core role j, a height"
  | .result_9_1 => "Lemma 9.1: Lemma 9.1 (Sparse mass of separated progression tests). There are absolute constants C and Cres with the following property. There are four roles 0, 1, 2, 3, of which either four or exactly three"
  | .result_9_2 => "Proposition 9.2: Proposition 9.2 (Counts for the tested core tuples). There is an absolute p0 ∈(0, 1) such that, for the preceding data and some L0 ≤P C(1 + log(ν/µ))C, one has"
  | .result_9_3 => "Proposition 9.3: Proposition 9.3 (Powered estimate for the core terms). There are absolute ε > 0 and C4 < ∞, with 1 −ε > 2/3, such that the terms containing at least three core roles in the localized expansion"

def partialSourceComponentExists : PaperResult → Bool
  | .result_1_1 => true
  | .result_2_1 => true
  | .result_2_2 => true
  | .result_2_3 => true
  | .result_2_4 => true
  | .result_3_1 => true
  | .result_3_2 => true
  | .result_3_3 => true
  | .result_3_4 => true
  | .result_3_5 => true
  | .result_4_1 => true
  | .result_4_2 => true
  | .result_4_3 => false
  | .result_4_4 => false
  | .result_4_5 => false
  | .result_4_6 => false
  | .result_4_7 => false
  | .result_4_8 => false
  | .result_4_9 => false
  | .result_4_10 => false
  | .result_4_11 => false
  | .result_4_12 => false
  | .result_5_1 => false
  | .result_5_2 => false
  | .result_5_3 => true
  | .result_5_4 => false
  | .result_5_5 => false
  | .result_5_6 => false
  | .result_5_7 => false
  | .result_5_8 => false
  | .result_6_1 => false
  | .result_6_2 => false
  | .result_6_3 => false
  | .result_6_4 => false
  | .result_6_5 => false
  | .result_6_6 => false
  | .result_6_7 => false
  | .result_6_8 => false
  | .result_6_9 => false
  | .result_7_1 => false
  | .result_7_2 => false
  | .result_7_3 => false
  | .result_7_4 => false
  | .result_7_5 => false
  | .result_8_1 => false
  | .result_8_2 => false
  | .result_8_3 => false
  | .result_8_4 => false
  | .result_8_5 => true
  | .result_8_6 => true
  | .result_8_7 => false
  | .result_8_8 => false
  | .result_8_9 => false
  | .result_8_10 => true
  | .result_8_11 => false
  | .result_8_12 => false
  | .result_9_1 => true
  | .result_9_2 => false
  | .result_9_3 => false

def mappedLeanFile : PaperResult → String
  | .result_1_1 => "OpenAI086/PaperStatement.lean"
  | .result_2_1 => "OpenAI086/LocalForms.lean"
  | .result_2_2 => "OpenAI086/UniformBootstrap.lean"
  | .result_2_3 => "OpenAI086/OuterStopping.lean"
  | .result_2_4 => "OpenAI086/OuterStopping.lean"
  | .result_3_1 => "OpenAI086/Packing.lean"
  | .result_3_2 => "OpenAI086/PrivateCoordinates.lean"
  | .result_3_3 => "OpenAI086/OrderedProductTelescoping.lean"
  | .result_3_4 => "OpenAI086/FiniteCompression.lean"
  | .result_3_5 => "OpenAI086/DyadicTails.lean"
  | .result_4_1 => "OpenAI086/QuadraticChartsElementary.lean"
  | .result_4_2 => "OpenAI086/QuadraticChartsElementary.lean"
  | .result_4_3 => "OpenAI086/PaperTargets/Result_4_3.lean"
  | .result_4_4 => "OpenAI086/PaperTargets/Result_4_4.lean"
  | .result_4_5 => "OpenAI086/PaperTargets/Result_4_5.lean"
  | .result_4_6 => "OpenAI086/PaperTargets/Result_4_6.lean"
  | .result_4_7 => "OpenAI086/PaperTargets/Result_4_7.lean"
  | .result_4_8 => "OpenAI086/PaperTargets/Result_4_8.lean"
  | .result_4_9 => "OpenAI086/PaperTargets/Result_4_9.lean"
  | .result_4_10 => "OpenAI086/PaperTargets/Result_4_10.lean"
  | .result_4_11 => "OpenAI086/PaperTargets/Result_4_11.lean"
  | .result_4_12 => "OpenAI086/PaperTargets/Result_4_12.lean"
  | .result_5_1 => "OpenAI086/PaperTargets/Result_5_1.lean"
  | .result_5_2 => "OpenAI086/PaperTargets/Result_5_2.lean"
  | .result_5_3 => "OpenAI086/ErrataChecks.lean"
  | .result_5_4 => "OpenAI086/PaperTargets/Result_5_4.lean"
  | .result_5_5 => "OpenAI086/PaperTargets/Result_5_5.lean"
  | .result_5_6 => "OpenAI086/PaperTargets/Result_5_6.lean"
  | .result_5_7 => "OpenAI086/PaperTargets/Result_5_7.lean"
  | .result_5_8 => "OpenAI086/PaperTargets/Result_5_8.lean"
  | .result_6_1 => "OpenAI086/PaperTargets/Result_6_1.lean"
  | .result_6_2 => "OpenAI086/PaperTargets/Result_6_2.lean"
  | .result_6_3 => "OpenAI086/PaperTargets/Result_6_3.lean"
  | .result_6_4 => "OpenAI086/PaperTargets/Result_6_4.lean"
  | .result_6_5 => "OpenAI086/PaperTargets/Result_6_5.lean"
  | .result_6_6 => "OpenAI086/PaperTargets/Result_6_6.lean"
  | .result_6_7 => "OpenAI086/PaperTargets/Result_6_7.lean"
  | .result_6_8 => "OpenAI086/PaperTargets/Result_6_8.lean"
  | .result_6_9 => "OpenAI086/PaperTargets/Result_6_9.lean"
  | .result_7_1 => "OpenAI086/PaperTargets/Result_7_1.lean"
  | .result_7_2 => "OpenAI086/PaperTargets/Result_7_2.lean"
  | .result_7_3 => "OpenAI086/PaperTargets/Result_7_3.lean"
  | .result_7_4 => "OpenAI086/PaperTargets/Result_7_4.lean"
  | .result_7_5 => "OpenAI086/PaperTargets/Result_7_5.lean"
  | .result_8_1 => "OpenAI086/PaperTargets/Result_8_1.lean"
  | .result_8_2 => "OpenAI086/PaperTargets/Result_8_2.lean"
  | .result_8_3 => "OpenAI086/PaperTargets/Result_8_3.lean"
  | .result_8_4 => "OpenAI086/PaperTargets/Result_8_4.lean"
  | .result_8_5 => "OpenAI086/EntryRankSummation.lean"
  | .result_8_6 => "OpenAI086/BadDensityChain.lean"
  | .result_8_7 => "OpenAI086/PaperTargets/Result_8_7.lean"
  | .result_8_8 => "OpenAI086/PaperTargets/Result_8_8.lean"
  | .result_8_9 => "OpenAI086/PaperTargets/Result_8_9.lean"
  | .result_8_10 => "OpenAI086/ComponentIntersections.lean"
  | .result_8_11 => "OpenAI086/PaperTargets/Result_8_11.lean"
  | .result_8_12 => "OpenAI086/PaperTargets/Result_8_12.lean"
  | .result_9_1 => "OpenAI086/FirstFailure.lean"
  | .result_9_2 => "OpenAI086/PaperTargets/Result_9_2.lean"
  | .result_9_3 => "OpenAI086/PaperTargets/Result_9_3.lean"

/-- This is metadata verification, not a paper theorem certificate. -/
theorem paper_result_catalog_has_59 : allPaperResults.length = 59 := by decide

theorem paper_result_catalog_nodup : allPaperResults.Nodup := by decide

theorem paper_partial_source_component_count_17 :
    (allPaperResults.filter partialSourceComponentExists).length = 17 := by decide

theorem paper_target_only_count_42 :
    (allPaperResults.filter (fun r => !(partialSourceComponentExists r))).length = 42 := by decide

end OpenAI086.PaperTargets
