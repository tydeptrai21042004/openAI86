#!/usr/bin/env python3
"""Exact rational regression checks for V4 finite-model arguments.

This does not parse Lean or execute Lean's kernel. It tests numeric models
of the mathematical claims and deliberately reports the scope.
"""
from fractions import Fraction as F
import random

rng = random.Random(86261122)
checks = 0

def dot(x, y):
    return sum((a*b for a,b in zip(x,y)), F(0))

def matrix_column(m, j):
    return [row[j] for row in m]

def apply_projection(H, r, x):
    out = [F(0) for _ in x]
    for j in range(r):
        c = matrix_column(H,j)
        alpha = dot(c,x)
        for i in range(len(x)):
            out[i] += alpha*c[i]
    return out

def diff(x,y):
    return [a-b for a,b in zip(x,y)]

def householder(d):
    v = [rng.randrange(-3,4) for _ in range(d)]
    if not any(v): v[0] = 1
    q = sum((e*e for e in v))
    return [[F(int(i==j))-F(2*v[i]*v[j],q) for j in range(d)] for i in range(d)]

for _ in range(1600):
    d = rng.randrange(2,6)
    H = householder(d)
    x = [F(rng.randrange(-5,6)) for _ in range(d)]
    start, step, count = (rng.randrange(0,4), rng.randrange(0,5), rng.randrange(0,5))
    max_ix = start + count * step + 3
    ranks = sorted(rng.randrange(d+1) for _ in range(max_ix+1))
    def P(k):
        return apply_projection(H,ranks[k],x)
    block = [diff(P(start+(k+1)*step),P(start+k*step)) for k in range(count)]
    energy = sum((dot(b,b) for b in block),F(0))
    boundary = dot(P(start+count*step),P(start+count*step))-dot(P(start),P(start))
    assert energy == boundary
    checks += 1
    assert energy <= dot(x,x)
    checks += 1
    # General monotone cuts with unequal lengths and repeated endpoints.
    cuts = sorted(rng.randrange(max_ix + 1) for _ in range(rng.randrange(1,9)))
    if not cuts:
        cuts = [0]
    # At least one pair of endpoints for a possibly empty family.
    if len(cuts) == 1:
        cuts.append(cuts[0])
    pieces = [diff(P(cuts[k+1]),P(cuts[k])) for k in range(len(cuts)-1)]
    variable_energy = sum((dot(z,z) for z in pieces), F(0))
    assert variable_energy == dot(P(cuts[-1]),P(cuts[-1]))-dot(P(cuts[0]),P(cuts[0]))
    checks += 1
    assert variable_energy <= dot(x,x)
    checks += 1
    # Disjoint, possibly different-length intervals.
    a = rng.randrange(0,max_ix)
    b = rng.randrange(a,max_ix)
    c = rng.randrange(b,max_ix)
    e = rng.randrange(c,max_ix+1)
    assert dot(diff(P(b),P(a)),diff(P(e),P(c))) == 0
    checks += 1
    # Different choices of blocks for different Parseval rows.
    if count:
        values = [dot(matrix_column(H,r),block[rng.randrange(count)]) for r in range(d)]
        assert sum((v*v for v in values),F(0)) <= dot(x,x)
        checks += 1

for _ in range(5000):
    u = rng.randrange(0,9)
    v = rng.randrange(0,9)
    a = [[F(rng.randrange(0,11),rng.randrange(1,5)) for _ in range(v)] for _ in range(u)]
    t = F(rng.randrange(-1,21),rng.randrange(1,6))
    rows = [sum(row,F(0)) for row in a]
    total_by_rows = sum(rows,F(0))
    total_by_cols = sum((a[i][j] for j in range(v) for i in range(u)),F(0))
    assert total_by_rows == total_by_cols
    checks += 1
    mass = sum((t for x in rows if t <= x),F(0))
    assert mass <= total_by_rows
    checks += 1

print({'status':'PASS', 'exact_rational_cases':checks,
       'scope':'aligned nested projections / disjoint block orthogonality / adaptive rows / bad-partner Markov',
       'lean_kernel_checked':False})
