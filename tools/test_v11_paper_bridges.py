#!/usr/bin/env python3
"""Finite regression for V11 manuscript-specific proof candidates.

These are *not* Lean kernel proofs. Integer rank bins and cardinalities
are exact, and all fractions use Fraction. Floating-point layer energy
checks only supplement the exact arithmetic.
"""
from __future__ import annotations
from fractions import Fraction
from random import Random

rng=Random(86011)
checks={'union_card':0,'rank_pointwise':0,'nested_grid':0,'density_chain':0,
        'true_premises':0,'layer_cs_exact':0,'counterexample_endpoint':0,
        'integer_log_bins':0}
BETA=Fraction(1,5)


def floor_log_11_10(k):
    if k == 0: return 0
    p,q=11,10
    rank=0
    while p<=k*q:
        rank+=1
        p*=11
        q*=10
    return rank


def density(S,C):
    if not C: return Fraction(0)
    return Fraction(len(S&C),len(C))


def bad(Pold,C,X,Y,beta=BETA):
    return int(floor_log_11_10(len(Pold)) != floor_log_11_10(len(C))
               or beta < density(X|Y,C))

# Finite integer-power bin matches floor(log_1.1(n)) on a broad checked
# domain, without floating-point logarithms.
for n in range(1,201):
    count=0
    p=q=1
    for _k in range(10*(n+1)):
        p*=11
        q*=10
        if p<=n*q: count+=1
    assert count == floor_log_11_10(n)
    checks['integer_log_bins']+=1

# The explicit missing P_N subset C_N condition matters: it is not a
# consequence of C_i subset P_(i+1) when i<N.
P0={0};C0={0};P1={0,1};C1=set()
assert C0 <= P1 and P0 <= C0 and not P1 <= C1
assert floor_log_11_10(len(C1))-floor_log_11_10(len(P1)) < 0
checks['counterexample_endpoint']+=1

for _ in range(16000):
    M=rng.randrange(1,26)
    a=set(rng.sample(range(M),rng.randrange(M+1)))
    b=set(rng.sample(range(M),rng.randrange(M+1)))
    c=set(rng.sample(range(M),rng.randrange(M+1)))
    assert len((a|b)&c) <= len(a&c)+len(b&c)
    assert density(a|b,c)<=density(a,c)+density(b,c)
    checks['union_card']+=1
    Pold=set(rng.sample(range(M),rng.randrange(M+1)))
    Pnew=Pold|set(rng.sample(range(M),rng.randrange(M+1)))
    C=Pnew|set(rng.sample(range(M),rng.randrange(M+1)))
    r0,r1,r2=map(lambda z:floor_log_11_10(len(z)),(Pold,Pnew,C))
    score=(r1-r0)+(r2-r1)+(density(a,C)+density(b,C))/BETA
    assert bad(Pold,C,a,b)<=score,(Pold,Pnew,C,a,b,score)
    checks['rank_pointwise']+=1

# Concrete i,h label sets. The set sizes increase with both axes and
# C_i,h lies between P_i,h and P_(i+1),h including final C_N,h.
for _ in range(3000):
    N=rng.randrange(0,8)
    H=rng.randrange(1,26)
    lag=rng.randrange(0,5)
    M=rng.randrange(3,80)
    a=rng.randrange(1,12)
    b=rng.randrange(0,5)
    c=rng.randrange(0,a+1)
    base=rng.randrange(1,4)
    def P(i,h): return set(range(min(M,base+a*i+b*h)))
    def C(i,h): return set(range(min(M,base+a*i+b*h+c)))
    X=[set(rng.sample(range(M),rng.randrange(0,min(M,4)+1))) for _ in range(N+1)]
    Y=[[set(rng.sample(range(M),rng.randrange(0,min(M,3)+1)))
        for h in range(H)] for _i in range(N+1)]
    for i in range(N+1):
        for h in range(H+lag+1):
            assert P(i,h)<=C(i,h)
            assert P(i,h)<=P(i,h+1)
            if i<N: assert C(i,h)<=P(i+1,h)
    L=max(floor_log_11_10(len(C(i,h))) for i in range(N+1) for h in range(H+lag+1))
    for i in range(N+1):
        vertical=Fraction(0)
        ymass=Fraction(0)
        for h in range(H):
            pn,pnext,cnow=map(lambda z:floor_log_11_10(len(z)),
                              (P(i,h),P(i,h+lag),C(i,h+lag)))
            ymass+=density(Y[i][h],C(i,h+lag))
            score=(pnext-pn)+(cnow-pnext)+(
                density(X[i],C(i,h+lag))+density(Y[i][h],C(i,h+lag)))/BETA
            assert bad(P(i,h),C(i,h+lag),X[i],Y[i][h])<=score
            vertical += pnext-pn
        assert vertical<=lag*L
    for h in range(H):
        horizontal=sum(floor_log_11_10(len(C(i,h+lag)))-
                       floor_log_11_10(len(P(i,h+lag))) for i in range(N+1))
        assert horizontal<=L
    A=max(sum(density(Y[i][h],C(i,h+lag)) for h in range(H)) for i in range(N+1))
    B=max(sum(density(X[i],C(i,h+lag)) for i in range(N+1)) for h in range(H))
    badcounts=[sum(bad(P(i,h),C(i,h+lag),X[i],Y[i][h]) for h in range(H))
               for i in range(N+1)]
    # Independent check of the summed upper bound proved in the Lean bridge.
    assert sum(badcounts) <= (N+1)*(lag*L+A/BETA)+H*(L+B/BETA)
    checks['nested_grid']+=1
    delta=Fraction(1,8)
    if 2*(lag*L + A/BETA)<=delta*H and all(delta*H <= x for x in badcounts):
        assert N+1<= 2*(L+B/BETA)/delta
        checks['true_premises']+=1
    checks['density_chain']+=1

# Non-vacuous stress case satisfying ALL hypotheses of the final bound.
N,H,lag,M=3,512,1,16
P=lambda i,h:set(range(min(M,1+3*i+h)))
C=lambda i,h:set(range(min(M,2+3*i+h)))
X=[{0} for _ in range(N+1)]
Y=[[set() for _ in range(H)] for _ in range(N+1)]
L=floor_log_11_10(M)
A=Fraction(0)
B=max(sum(density(X[i],C(i,h+lag)) for i in range(N+1)) for h in range(H))
delta=Fraction(1,2)
beta=Fraction(1,32)
badcounts=[sum(bad(P(i,h),C(i,h+lag),X[i],Y[i][h],beta) for h in range(H)) for i in range(N+1)]
assert 2*(lag*L+A/BETA)<=delta*H
assert all(delta*H<=z for z in badcounts)
assert N+1<=2*(L+B/beta)/delta
checks['true_premises']+=1

# Exact finite-dimensional Cauchy--Schwarz for the m layer terms, over
# variable depths and dimensions; the factor m is attained by identical v.
for _ in range(3000):
    T=rng.randrange(1,9); m=rng.randrange(1,9); d=rng.randrange(1,9)
    v=[[[rng.randrange(-6,7) for _j in range(d)] for _i in range(m)]
        for _n in range(T)]
    lhs=sum(sum(sum(v[n][i][j] for i in range(m))**2 for j in range(d))
            for n in range(T))
    rhs=m*sum(v[n][i][j]**2 for n in range(T) for i in range(m)
              for j in range(d))
    assert lhs<=rhs
    checks['layer_cs_exact']+=1

print('V11 exact manuscript-bridge regressions PASS',checks,'total=',sum(checks.values()))
