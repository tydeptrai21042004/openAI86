#!/usr/bin/env python3
"""Exact finite regression models, not Lean proofs."""
from fractions import Fraction as Q
from random import Random
r = Random(86)
n = 0
# scalar absorption
for K in range(1, 10):
    for A in range(0, 10):
        for c in (Q(0), Q(1, 4*K), Q(1, 2*K)):
            for CN in range(0, 2*K*A+3):
                if CN <= K*(A+c*CN):
                    assert CN <= 2*K*A
                n += 1
# logarithmic packet cover with exact integer coordinates (arbitrary widths)
for _ in range(300):
    d=r.randint(1, 7); W=r.randint(0, 12); U=r.randint(0, 30); l=r.randint(1, 5)
    centers=[r.randint(-100,100) for _ in range(d)]
    E={a+j for a in centers for j in range(-W,W+1)}
    S={k for k in range(-200,201) if any(0 <= v-l*k <= U for v in E)}
    assert len(S) <= d*(2*W+U+1)
    n += 1
# weighted clipped core terms at p=1/2; use perfect squares
from math import isqrt
for _ in range(300):
    eta=r.randint(0,15)**2
    B=E=L=0
    for _ in range(r.randint(0,10)):
        w=r.randint(0,10); xs=[r.randint(0,20)**2 for _ in range(r.randint(0,7))]
        e=r.randint(0,20); a=sum(xs)+e
        B+=w*sum(isqrt(x) for x in xs); E+=w*e; L+=w*min(eta,a)
    assert L <= isqrt(eta)*B+E
    n += 1
# same-event inclusion, including terminal position
for _ in range(300):
    mode=set(range(10)); pi={x:r.randint(0,4) for x in mode}
    for _ in range(r.randint(1,8)):
        pre={x for x in mode if r.randrange(2)}; cur=pre | {x for x in mode if r.randrange(2)}
        assert {pi[x] for x in pre} <= {pi[x] for x in cur}
    n += 1
print(f'PASS: {n} exact finite V61 regression cases (not kernel certificates)')
