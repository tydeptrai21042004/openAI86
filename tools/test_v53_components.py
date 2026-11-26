#!/usr/bin/env python3
"""Exact arithmetic models; not proof certificates."""
from fractions import Fraction as F
from math import ceil
from random import Random
r=Random(53)
counts={'ceiling':0,'polynomial_side':0,'sparse_exponents':0,'large_density':0,'integral_error':0}
# eta^(-alpha) is modeled by a positive rational x >= 1; C integer.
for _ in range(400):
    x=F(r.randint(1,200),r.randint(1,200)); x=max(x,1/x)
    p=ceil(x); c=r.randint(0,12)
    assert x<=p<=2*x and p**c<=2**c*x**c
    counts['ceiling']+=1
# P=t^8, beta=1/(8*C5); take C0=a^(8*C5) and K+2=b^(8*C5).
for _ in range(400):
    t=r.randint(1,6); a=r.randint(1,4); c5=r.randint(1,5); b=r.randint(1,a*t)
    P=t**8; C0=a**(8*c5); K=b**(8*c5)-2; G=r.randint(0,t)
    assert K+2<=C0*P**c5 and G<=t
    assert F(G*b,t**4)<=F(a,t**2)
    counts['polynomial_side']+=1
# delta=t^2080, alpha=t^2, kappa=t^4, hence three exact powers t^2,t,t^104.
for _ in range(150):
    t=F(r.randint(1,12),r.randint(12,24)); a=t*t; k=a*a
    L=r.randint(1,8)**2; rootL=int(L**0.5); ell=r.randint(1,10)
    assert k/a==t*t and a**-4*k**-24*t**208==t**104
    assert L*k/a+rootL*t+ell*L**29*t**104<=3*ell*L**29*t
    counts['sparse_exponents']+=1
    t0=t/2; assert 1/t0*t>=1
    counts['large_density']+=1
# A finite measure space with rational weights and signs, exact L1 error.
for _ in range(500):
    n=r.randint(1,12); u=r.choice([-1,1]); weights=[F(r.randint(1,8),8) for i in range(n)]
    g=[F(r.randint(-10,10),4) for i in range(n)]; e=[F(r.randint(-10,10),8) for i in range(n)]
    f=[u*x+y for x,y in zip(g,e)]
    assert abs(sum(w*x for w,x in zip(weights,f))-u*sum(w*x for w,x in zip(weights,g)))<=sum(w*abs(x) for w,x in zip(weights,e))
    counts['integral_error']+=1
print(counts, 'total:',sum(counts.values()))
