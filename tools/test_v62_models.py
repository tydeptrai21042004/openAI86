#!/usr/bin/env python3
"""Exact rational/integer models of V62 deductions; not Lean verification."""
from fractions import Fraction as Q
from random import Random
from math import isqrt
rng = Random(862)
n = 0
# Exact natural floor log base 11/10, no floating point near boundaries.
levels = [Q(1)]
while levels[-1] <= 400:
    levels.append(levels[-1]*Q(11,10))
from bisect import bisect_right
rank = {k: bisect_right(levels,k)-1 for k in range(1,401)}
for a in range(1,401):
    for b in range(a,401):
        if 10*a < 9*b:
            assert rank[a] != rank[b]
            n += 1
# Complementary bad-label fraction; exact inequality, including zero good labels.
for c in range(1,101):
    for g in range(c+1):
        if 10*g < 9*c:
            for bad in (c-g,c):
                assert Q(bad,c) > Q(1,10)
                n += 1
# Log-packet exceptional blocks on a K-spaced path; endpoints strictly excluded.
for _ in range(1000):
    d = rng.randint(1,8); W = rng.randint(0,12); tau = rng.randint(0,8)
    K = max(1,W+2*tau)+rng.randint(0,5); b0 = rng.randint(-50,50)
    centers = [rng.randint(-120,120) for _ in range(d)]
    vals = {p+j for p in centers for j in range(W+1)}
    B = {j for j in range(-150,151) if any(b0+j*K-2*K-tau < v < b0+j*K+K+tau for v in vals)}
    assert len(B) <= 4*d
    n += 1
# Finite Tonelli and weighted clipped core sum on a depth-three binary tree.
for _ in range(1000):
    cells = [(h,j) for h in range(4) for j in range(2**h)]
    leaves = list(range(8)); w = {l:rng.randint(0,8) for l in leaves}
    inc = lambda i,l: l//2**(3-i[0])==i[1]
    x = {i:[rng.randint(0,15)**2 for _ in range(rng.randint(0,4))] for i in cells}
    err = {i:rng.randint(0,9) for i in cells}; eta = rng.randint(0,16)**2
    a = {i:sum(x[i])+err[i] for i in cells}
    wi = {i:sum(w[l] for l in leaves if inc(i,l)) for i in cells}
    pwr = {i:sum(map(isqrt,x[i])) for i in cells}
    assert sum(wi[i]*a[i] for i in cells)==sum(w[l]*sum(a[i] for i in cells if inc(i,l)) for l in leaves)
    B = max(sum(pwr[i] for i in cells if inc(i,l)) for l in leaves)
    E = max(sum(err[i] for i in cells if inc(i,l)) for l in leaves)
    assert sum(wi[i]*min(eta,a[i]) for i in cells) <= (isqrt(eta)*B+E)*sum(w.values())
    n += 1
# Leakage energy with arbitrary overlapping path-event supports and colours.
for _ in range(1000):
    L = list(range(8)); w = [rng.randint(0,6)**2 for _ in L]
    events = [set(l for l in L if rng.randrange(2)) for _ in range(rng.randint(1,12))]
    B = max(sum(l in e for e in events) for l in L); eps = rng.randint(0,5)
    lengths = [sum(w[l] for l in e) for e in events]
    errs = [eps*isqrt(t) for t in lengths]
    assert sum(lengths) <= B*sum(w)
    assert sum(e*e for e in errs) <= eps*eps*B*sum(w)
    n += 1
print(f'PASS: {n} exact finite V62 regression cases (not kernel certificates)')
