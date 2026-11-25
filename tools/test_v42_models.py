#!/usr/bin/env python3
"""Exact finite model checks and high-precision tail checks; not Lean proofs."""
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from random import Random
rng=Random(42)
checks=0
# Complex integers represented as pairs, so both synthesis energies are exact.
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def sq(a): return a[0]**2+a[1]**2
for _ in range(1200):
    n=rng.randint(1,12); budget=max(n,5); c=[(rng.randint(-5,5),rng.randint(-5,5)) for _ in range(n)]
    phi=[(rng.randint(-2,2),rng.randint(-2,2)) for _ in range(n)]
    a=[F(rng.randint(1,budget),budget) for _ in range(n)]
    physical=tuple(sum(x[j] for x in map(mul,c,phi)) for j in (0,1))
    e=sq(physical)+sum(ai**2*sq(ci) for ai,ci in zip(a,c)); en=sum(map(sq,c))
    assert F(en,budget**2)<=e<=budget**3*en
    checks+=1
# Actual qualifying windows from the coordinate magnitudes and height <= 2.
for k in range(150):
    L=k+1; v1=F(1); v2=F(2)**(3*L); beta=F(2)**L
    A={n for n in range(-L,3*L+1) if any(1<=F(2)**(-n)*v<=beta for v in (v1,v2))}
    assert len(A)==2*L+2 and len(A)>k+L+1
    checks+=1
# The weighted tails are checked at finite cutoffs with Decimal arithmetic.
# Their infinite control follows only from the mathematical proof candidate.
with localcontext() as ctx:
    ctx.prec=60
    for m in (1,2,12,31):
        for delta in (D('0.5'),D('0.05'),D('0.005'),D('0.0005')):
            u=max(D(3),2*D(m)/delta)
            terms=sum((D(n+m)*(-u*(D(2)**n)).exp() for n in range(12)),D(0))
            assert terms<=delta
            checks+=1
print(f'V42: {checks} model checks passed (1350 exact, 16 high-precision finite-tail checks).')
