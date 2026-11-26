#!/usr/bin/env python3
"""Exact regression models for V59; not a Lean proof or numerical evidence of completion."""
from fractions import Fraction as F
from itertools import product
from random import Random
import json

rng = Random(59)
counts = {}
# Half-open overlap at endpoints agrees with the interval to the right.
for _ in range(600):
    ints = [(F(rng.randrange(-50, 51), 7), F(rng.randrange(-50, 51), 7)) for _ in range(rng.randrange(1, 21))]
    ends = sorted({x for ab in ints for x in ab})
    card = lambda y: sum(a <= y < b for a,b in ints)
    for a,b in zip(ends, ends[1:]):
        assert card(a) == card((a+b)/2)
    assert card(ends[-1]) == 0
counts['halfopen_overlap'] = 600
# Exact radial clipping for complex vectors with rational known norm
# (3-4-5 and scaled variants); no floating-point comparisons.
for _ in range(600):
    r = F(rng.randrange(0, 101), rng.randrange(1, 11))
    A = F(rng.randrange(1, 101), rng.randrange(1, 11))
    x,y = 3*r/5,4*r/5
    k = min(F(1), A/r) if r else F(1)
    clipped = (k*x,k*y)
    error = max(F(0), r-A)
    assert clipped[0]**2+clipped[1]**2 == min(r,A)**2
    assert (x-clipped[0])**2+(y-clipped[1])**2 == error**2
    assert error <= r*r/A
counts['radial_clipping'] = 600
# Verify the manuscript's depth rectangles and designated mask separation.
# A rectangle is a tuple (kind, attaining/upper slots, heavy, level, position).
def rect(d):
    v = min(d); S = tuple(i for i,t in enumerate(d) if t == v)
    if len(S)>=2: return ('rep',S,S[0],0,v)
    a=S[0]; w=min(d[j] for j in range(4) if j != a)
    h=(v^w).bit_length()-1; k=v//(2**(h+1)); U=tuple(j for j in range(4) if j!=a and d[j]//2**h==2*k+1)
    return ('uniq',U,a,h,k)
def side(R,j,x):
    kind,S,a,h,k=R
    if kind=='rep': return x==k if j in S else x>k
    if j==a: return x//2**h==2*k
    return x//2**h==2*k+1 if j in S else x//2**h>=2*k+2
rects=set()
for d in product(range(8),repeat=4):
    R=rect(d);rects.add(R)
    assert all(side(R,j,x) for j,x in enumerate(d))
for d in product(range(8),repeat=4):
    assert sum(all(side(R,j,x) for j,x in enumerate(d)) for R in rects)==1
counts['rectangle_partition'] = 8**4
for R in rects:
    kind,S,a,h,k=R
    b=S[1] if kind=='rep' else S[0]
    for R1 in rects:
        if R1!=R and R1[:4]==R[:4]:
            assert all(not(side(R,a,x) and side(R1,a,x)) for x in range(8))
            assert all(not(side(R,b,x) and side(R1,b,x)) for x in range(8))
counts['rectangle_mask_levels'] = len(rects)
# exponent comparison in the short-block bridge
for _ in range(500):
    q=F(2)+F(rng.randrange(1,100),100)
    assert 0 < 2*(q-2)/(q-1) <= 2*(q-2)
counts['shortblock_exponent'] = 500
print(json.dumps({'kind':'exact_model_regressions_not_kernel_proofs','counts':counts,'total':sum(counts.values())},indent=2))
