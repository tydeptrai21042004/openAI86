# Standalone mathematical derivation of Lemma 3.3

This is a *mathematical derivation* from the assumptions in the PDF.
It does not claim independent authorship of the separately supplied Lean code.

## Setting

Let `X` be a Hilbert space. For each layer `i=1,...,m` let
`P^i_0,...,P^i_T` be increasing orthogonal projections. Layers may **not**
commute with each other. Let `Z_n = P^m_n ... P^1_n`.
Put `L=1+ceil(log_2(T+1))`.

Suppose the row maps `B_ν : X -> Y_ν` satisfy for every `h in X`:

```
 sum_ν ||B_ν h||² <= ||h||².
```

## Step A: a one-layer logarithmic row bound

Write `Δ_0=P_0` and `Δ_j=P_j-P_{j-1}` for `j>=1`.
For an increasing family of orthogonal projections,
all `Δ_j` are mutually orthogonal projections and

```
P_n = Σ_{j=0}^n Δ_j,
Σ_{j=0}^T ||Δ_j h||² = ||P_T h||² <= ||h||².
```

Choose a dyadic decomposition of every prefix `[0,n]` into complete
blocks; at most one block of each length is needed. For a fixed block
length the complete blocks are disjoint, hence the corresponding
`Δ`-sums are mutually orthogonal. Applying row contraction and Bessel's
inequality to each block length and Minkowski in the direct row sum gives

```
 (Σ_ν ||B_ν P_{n(ν)} h||²)^(1/2) <= L ||h||.
```

The constant depends only logarithmically on the horizon, not on the
number of Bessel rows.

## Step B: noncommuting products

Assume the estimate for `m-1` layers. Set

```
 B'_ν = L^(-1) B_ν P^m_{n(ν)}.
```

Step A, applied with the row maps `B_ν`, shows that
`Σ_ν ||B'_ν h||² <= ||h||²` for all `h`.

Apply the induction hypothesis to the product of the first `m-1`
layers with row maps `B'_ν`. Undoing the `L^(-1)` scaling yields

```
 (Σ_ν ||B_ν Z_{n(ν)} g||²)^(1/2) <= L^m ||g||,
```

or its square with factor `L^(2m)`.
This step never interchanges projections belonging to different layers.

## Step C: square-summed successive jumps

A telescoping identity in the **specified order** is

```
Z_n - Z_{n-1}
 = Σ_{i=1}^m (P^m_n ... P^{i+1}_n)
       (P^i_n - P^i_{n-1})
       (P^{i-1}_{n-1} ... P^1_{n-1}).
```

All factors on the left of the increment are contractions.
For each fixed `i`, the difference operators
`P^i_n-P^i_{n-1}` are pairwise orthogonal projections as `n` varies,
and hence their maps form a Bessel row. Step B on the `i-1` right-hand
layers (with index `n-1`) gives the square-summed norm of the `i`-th
summand at most `L^(i-1)||g||`.

By Minkowski and `L>=1`:

```
(Σ_{n=1}^T ||(Z_n-Z_{n-1})g||²)^(1/2)
 <= Σ_{i=1}^m L^(i-1)||g||
 <= m L^(m-1)||g||.
```

Squaring proves the second assertion of Lemma 3.3.
For `m=0`, the product is the identity and the increments vanish.

## The gap between source and current Lean encoding

The paper has possibly different row targets `Y_ν`. The candidate Lean
code uses a common output space `F`. This is a real scope difference,
though a formal construction of a common Hilbert direct sum can in
principle bridge it. That construction still needs its own proof.

The script implementing this argument was adapted under Apache-2.0 from
the credited reference; therefore it is **not independent proof authorship**.
A real `lake build` and checking `#print axioms` remain required.
