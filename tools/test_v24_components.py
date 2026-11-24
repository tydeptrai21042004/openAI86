#!/usr/bin/env python3
"""Exact Fraction regressions of the algebra in V24, not Lean proofs."""
from fractions import Fraction as Q
import random
rng = random.Random(86124)
counts = {}
def check(key, expr):
    assert expr, key
    counts[key] = counts.get(key, 0) + 1
# Arbitrary rectangular bilinear forms on two bands; include terminal band.
for P in range(1, 13):
    w = [Q(P-i,P) for i in range(P+1)]
    check('terminal weight', w[-1] == 0)
    for _ in range(50):
        h = [[Q(rng.randint(-30,30),rng.randint(1,9)) for j in w] for i in w]
        lhs = sum(w[j]*h[i][j]-w[i]*h[i][j] for i in range(P+1) for j in range(P+1))
        rhs = sum(Q(i-j,P)*h[i][j] for i in range(P+1) for j in range(P+1))
        check('band transfer', lhs == rhs)
# Minimum inequality for p=1/2 (exact square) and p=1.
for _ in range(2000):
    eta=Q(rng.randint(1,100),rng.randint(1,50))
    a=Q(rng.randint(0,100),rng.randint(1,50))
    b=Q(rng.randint(0,100),rng.randint(1,50))
    check('absolute error split', min(eta,a+b)<=min(eta,a)+b)
    check('half power exact', min(eta,a)**2<=eta*a)
    check('unit power', min(eta,a)<=a)
for n in range(31):
    for r in [Q(0),Q(1,16),Q(1,8),Q(1,4)]:
        check('finite restart geometric', sum(r**j for j in range(n))<=Q(4,3)*(1-r**n))
# Admissible finite level absorption, sampled without conditioning on conclusion.
for _ in range(1200):
    b=Q(rng.randint(0,10),20)
    A=Q(rng.randint(0,40),7); B=Q(rng.randint(0,40),9)
    C=(A+B+b)/(1-b)*Q(rng.randint(0,10),10)
    a=[b/4]*4
    cost=[x*(1+C) for x in a]
    check('level absorption', C<=A+B+sum(cost) and C<=2*(A+B+b))
print('V24 exact model assertions:',counts)
print('TOTAL',sum(counts.values()),'PASS (not Lean kernel verification)')
