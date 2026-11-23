#!/usr/bin/env python3
"""V12 independent exact-arithmetic regressions, not Lean kernel certification.

Paper (Oct 5 2026), Lemmas 8.5--8.6: exact 11/10 logarithmic bins,
per-label first-entry ranks, union-based bad-height test, and both-axis
incidence-to-chain counting. No floating-point approximations are used.
"""
from fractions import Fraction
from itertools import product
from math import prod

checks = 0

def check(p, desc):
    global checks
    checks += 1
    if not p:
        raise AssertionError(f"{desc}; check={checks}")

def rank(n, extra=0):
    """V11 definition: the exact 10(n+1) threshold window, optionally enlarged."""
    assert n >= 0
    cap = 10 * (n + 1) + extra
    a, b, total = 11, 10, 0
    for _ in range(cap):
        if a <= n * b:
            total += 1
        a *= 11
        b *= 10
    return total

def rank_fast(n):
    if not n:
        return 0
    a, b, total = 11, 10, 0
    while a <= n*b:
        total += 1
        a *= 11
        b *= 10
    return total

def normfrac(A,C):
    return Fraction(len(A & C),len(C)) if C else Fraction(0)

def harm(M):
    return sum((Fraction(1,k) for k in range(1,M+1)),Fraction(0))

# Rank completeness, monotonicity, initial segment and window independence.
previous = 0
for n in range(129):
    actual = rank_fast(n)
    standard = rank(n)
    check(actual == standard, f"rank complete n={n}")
    check(rank(n,extra=50) == standard, f"rank stable n={n}")
    check(standard <= 10*(n+1), f"bin bound n={n}")
    check(previous <= standard, f"monotonic n={n}")
    previous = standard
    for k in range(max(actual-2,0),actual+3):
        passed = 11**(k+1) <= n*10**(k+1)
        check(passed == (k<actual), f"rank initial segment n={n},k={k}")

for k in range(1500):
    check((k+10)*10**k <= 10*11**k, f"Bernoulli k={k}")

# Lemma 8.5: monotone prefix sets and arbitrary exceptional histories,
# with each label activated at most A times. All arithmetic is exact.
for M in range(1,12):
    for T in range(1,12):
        C = [set(range(min(M, 1+(t*M)//T))) for t in range(T)]
        for pattern in range(32):
            X = []
            for t in range(T):
                X.append({r for r in C[t] if ((pattern >> (r%5)) + t + 2*r)%4 == 0})
            A = max(sum(r in X[t] for t in range(T)) for r in range(M))
            lhs = sum((normfrac(X[t],C[t]) for t in range(T)),Fraction(0))
            check(lhs <= A*harm(M), f"entry rank budget M={M},T={T},pat={pattern}")
            for t in range(T):
                for r in X[t]:
                    check(r+1<=len(C[t]),"first-entry prefix cardinality")

# Two-axis model of the actual union predicate and pointwise inequality.
beta = Fraction(1,3)
for M in range(1,12):
    for N in range(1,5):
        H, lag = 7, 1
        P = [[set(range(min(M,1+i+h))) for h in range(H+lag+1)] for i in range(N+1)]
        C = P
        for pattern in range(10):
            X = [{r for r in range(M) if (r+i+pattern)%3==0} for i in range(N+1)]
            Y = [[{r for r in range(M) if (r+2*h+pattern)%4==0}
                  for h in range(H)] for i in range(N+1)]
            for i,h in product(range(N+1),range(H)):
                old,pnew,c = P[i][h],P[i][h+lag],C[i][h+lag]
                assert old <= pnew <= c
                unionfrac = normfrac(X[i]|Y[i][h],c)
                ub = normfrac(X[i],c)+normfrac(Y[i][h],c)
                bad = int(rank(len(old))!=rank(len(c)) or unionfrac>beta)
                point = rank(len(pnew))-rank(len(old)) +rank(len(c))-rank(len(pnew)) +ub/beta
                check(unionfrac<=ub,f"union density M={M},N={N},h={h}")
                check(bad<=point,f"pointwise bad M={M},N={N},h={h}")
                check(rank(len(c))<=rank(M),f"log cap M={M},N={N},h={h}")

# Non-vacuous chain example: all labels exceptional across positions,
# so every tested height is bad, but heightRank and occurrence bounds hold.
M,N,H,lag=4,2,300,1
C = [[set(range(M)) for _ in range(H+lag+1)] for _ in range(N+1)]
P=C
X = [set(range(M)) for _ in range(N+1)]
Y = [[set() for _ in range(H)] for _ in range(N+1)]
delta=Fraction(1,2)
A=Fraction(0)
B=Fraction(N+1)
beta=Fraction(1,3)
L=rank(M)
HB=harm(M)
for h in range(H):
    check(sum(normfrac(X[i],C[i][h+lag]) for i in range(N+1)) <= B*HB,
          f"horizontal exception budget h={h}")
for i in range(N+1):
    check(sum(normfrac(Y[i][h],C[i][h+lag]) for h in range(H)) <= A*HB,
          f"vertical exception budget i={i}")
    count=sum(int(rank(len(P[i][h])) != rank(len(C[i][h+lag])) or
                  normfrac(X[i]|Y[i][h],C[i][h+lag]) > beta) for h in range(H))
    check(Fraction(count)>=delta*H,"positive bad density")
check(2*(lag*L + A*HB/beta)<=delta*H,"absorption hypothesis non-vacuous")
check(N+1<=2*(L+B*HB/beta)/delta,"chain length conclusion non-vacuous")

# Endpoint is essential: the last P_i need not lie in C_i under i < N alone.
P0,C0,P1,C1={0},{0},{0},{1}
check(P0<=C0 and C0<=P1 and not P1<=C1,"missing terminal inclusion counterexample")
print(f"V12 exact integer/rational regressions: {checks:,} passed; no Lean kernel build")
