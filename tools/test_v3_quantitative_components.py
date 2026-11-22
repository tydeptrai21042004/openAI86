#!/usr/bin/env python3
"""Numerical/exact-arithmetic stress tests for independently authored V3 lemmas.

This checks mathematical models, not Lean parsing, elaboration or kernel correctness.
All random tests use an explicit seed and dimension/rounding tolerances.
"""
from fractions import Fraction
import numpy as np
import random

rng = np.random.default_rng(20261122)
prng = random.Random(20261122)
counts = {
    'private_gram_two_sided': 0,
    'long_range_projection_nesting': 0,
    'orthogonal_projection_increments': 0,
    'projection_window_energy': 0,
    'adaptive_row_bessel': 0,
    'multilevel_row_bessel': 0,
    'common_neighbor_double_count': 0,
    'common_neighbor_second_moment': 0,
    'exact_fraction_common_neighbor': 0,
    'four_step_walk_double_count': 0,
    'four_step_walk_second_moment': 0,
    'four_step_walk_density': 0,
    'noncommuting_layered_bessel': 0,
}

def check_le(a,b,eps=2e-8):
    assert a <= b + eps * (1 + abs(a) + abs(b)), (a,b)

def orthonormal(n):
    m = rng.normal(size=(n,n))
    q,_ = np.linalg.qr(m)
    return q

for _ in range(1200):
    n = int(rng.integers(1,13))
    D = float(rng.uniform(max(2,n), max(2,n)+12))
    eps = rng.uniform(1/D, D * .65, size=n)
    phi = rng.uniform(-1,1,size=n)*np.sqrt(np.maximum(0,D*D-eps*eps))
    c = rng.normal(size=n)
    value = (c@phi)**2 + np.dot(eps*c,eps*c)
    lower = np.dot(c/D,c/D)
    upper = D**3 * np.dot(c,c)
    check_le(lower,value)
    check_le(value,upper)
    counts['private_gram_two_sided']+=1

for _ in range(800):
    n = int(rng.integers(1,11))
    count = int(rng.integers(1,15))
    q=orthonormal(n)
    dims=np.sort(rng.integers(0,n+1,size=count+1))
    proj=[q[:,:d]@q[:,:d].T for d in dims]
    x=rng.normal(size=n)
    for i in range(count+1):
        for j in range(i,count+1):
            assert np.linalg.norm(proj[i]@proj[j]-proj[i]) < 2e-8
            counts['long_range_projection_nesting']+=1
    increments=[(proj[t+1]-proj[t])@x for t in range(count)]
    for k in range(count):
        for l in range(k+1,count):
            assert abs(increments[k] @increments[l]) < 2e-8
            counts['orthogonal_projection_increments']+=1
    i=int(rng.integers(0,count+1))
    j=int(rng.integers(i,count+1))
    left=sum(v@v for v in increments[i:j])
    right=np.linalg.norm(proj[j]@x)**2 - np.linalg.norm(proj[i]@x)**2
    assert abs(left-right) < 2e-8
    check_le(left,x@x)
    counts['projection_window_energy']+=1

for _ in range(900):
    n=int(rng.integers(1,10))
    nr=int(rng.integers(1,20))
    nb=int(rng.integers(1,8))
    nl=int(rng.integers(1,12))
    x=rng.normal(size=n)
    b=rng.normal(size=(nr,n))
    op=np.linalg.norm(b,ord=2)
    b=b/max(1,op)
    outputs=np.zeros(nr)
    for lev in range(nl):
        q=orthonormal(n)
        groups=rng.integers(0,nb,size=n)
        signals=[q[:,groups==block]@(q[:,groups==block].T@x) for block in range(nb)]
        energy=sum(v@v for v in signals)
        check_le(energy,x@x)
        choices=rng.integers(0,nb,size=nr)
        rows=np.array([b[r]@signals[choices[r]] for r in range(nr)])
        check_le(rows@rows,x@x)
        outputs+=rows
        counts['adaptive_row_bessel']+=1
    check_le(outputs@outputs,nl*nl*(x@x))
    counts['multilevel_row_bessel']+=1

for _ in range(400):
    n=int(rng.integers(1,12))
    blocks=int(rng.integers(1,5))
    layers=int(rng.integers(1,6))
    x=rng.normal(size=n)
    states=[x]
    for _layer in range(layers):
        q=orthonormal(n)
        groups=rng.integers(0,blocks,size=n)
        operators=[q[:,groups==k]@q[:,groups==k].T for k in range(blocks)]
        states=[p@y for y in states for p in operators]
    check_le(sum(y@y for y in states),x@x)
    counts['noncommuting_layered_bessel']+=1

for _ in range(1200):
    nu=int(rng.integers(0,17))
    nv=int(rng.integers(0,17))
    a=rng.integers(0,2,size=(nu,nv))
    codegrees=int((a@a.T).sum())
    deg=int((a.sum(axis=0)**2).sum())
    assert codegrees==deg
    counts['common_neighbor_double_count']+=1
    total=int(a.sum())
    assert total*total <= nv*codegrees
    counts['common_neighbor_second_moment']+=1
    total_four=int(((a@a.T)**2).sum())
    walked_four=sum(int(a[u,v]*a[w,v]*a[u,t]*a[w,t])
        for u in range(nu) for w in range(nu) for v in range(nv) for t in range(nv))
    assert total_four==walked_four
    counts['four_step_walk_double_count']+=1
    assert codegrees*codegrees <= (nu*nu)*total_four
    counts['four_step_walk_second_moment']+=1
    assert total**4 <= nu**2*nv**2*total_four
    counts['four_step_walk_density']+=1

for _ in range(500):
    nu=prng.randrange(1,6)
    nv=prng.randrange(1,6)
    a=[[Fraction(prng.randint(-5,5),prng.randint(1,5)) for _ in range(nv)] for _ in range(nu)]
    lhs=sum(a[u][v]*a[w][v] for u in range(nu) for w in range(nu) for v in range(nv))
    rhs=sum(sum(a[u][v] for u in range(nu))**2 for v in range(nv))
    assert lhs==rhs
    total=sum(sum(a[u][v] for u in range(nu)) for v in range(nv))
    assert total**2<=nv*lhs
    counts['exact_fraction_common_neighbor']+=1

print({'status':'PASS (numeric/exact-model checks; NOT kernel)', 'cases':counts,'total':sum(counts.values())})
