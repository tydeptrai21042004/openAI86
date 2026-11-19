#!/usr/bin/env python3
"""Finite mathematical sanity tests for the new independent §§8--9 components.

This executes ordinary Python arithmetic, NOT Lean kernel verification.
All inequalities are checked on exhaustive small configurations or exact
rational randomized finite models. It cannot establish the universal theorems.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random
import json

rng = Random(86093)
checks = {'majority_overlap_cases':0,'quantitative_overlap_cases':0,
          'ranked_incidence_cases':0,'pair_incidence_cases':0,
          'proper_four_path_cases':0,'greedy_block_cases':0}

# Exhaustively check the inequalities for subsets of ambient sets of size ≤7.
for n in range(8):
    full=(1 << n)-1
    for a in range(1 << n):
        for b in range(1 << n):
            na=a.bit_count(); nb=b.bit_count(); ni=(a & b).bit_count()
            assert na+nb <= n+ni
            if n < 2*na and n < 2*nb:
                assert ni>0
                checks['majority_overlap_cases']+=1
            if 10*n < 11*na and 100*n < 121*nb:
                assert n < 10*ni
                checks['quantitative_overlap_cases']+=1

# Ranked-incidence lemma with completely exact fractions.
for _ in range(2500):
    m=rng.randint(1,10); tmax=rng.randint(1,14)
    sizes=[rng.randint(1,m) for _ in range(tmax)]
    active=[[r < sizes[t] and rng.choice([True,False]) for r in range(m)] for t in range(tmax)]
    counts=[sum(active[t][r] for t in range(tmax)) for r in range(m)]
    A=max(counts,default=0)
    weighted=sum((Q(1,sizes[t]) for t in range(tmax) for r in range(m) if active[t][r]),Q(0))
    harmonic=sum((Q(1,r+1) for r in range(m)),Q(0))
    assert weighted <= A*harmonic
    checks['ranked_incidence_cases']+=1

# Hypothesis (1) of Lemma 9.1: bounded pair incidences force total ≤LM².
for _ in range(2500):
    m=rng.randint(0,10); smax=rng.randint(0,14); L=rng.randint(0,8)
    data={}
    for a,b in product(range(m),repeat=2):
        slots=list(range(smax)); rng.shuffle(slots)
        data[(a,b)]=set(slots[:rng.randint(0,min(smax,L))])
    ns=[sum(s in data[(a,b)] for a,b in product(range(m),repeat=2)) for s in range(smax)]
    assert sum(ns) <= L*m*m
    keep={s for s in range(smax) if rng.choice([True,False])}
    assert sum(ns[s] for s in keep) <= L*m*m
    checks['pair_incidence_cases']+=1

# A proper edge coloring using a unique color for each edge is enough to
# test the deterministic-color lemma, even for paths with repeated vertices.
for U,V in [(range(2),range(3)),(range(3),range(2))]:
    for start in U:
        seen={}
        for v1,u2,v3,u4 in product(V,U,V,U):
            colors=((start,v1),(u2,v1),(u2,v3),(u4,v3))
            path=(v1,u2,v3,u4)
            assert colors not in seen or seen[colors]==path
            seen[colors]=path
            checks['proper_four_path_cases']+=1

for _ in range(1000):
    blocks=rng.randint(0,50)
    alpha=Q(rng.randint(2,25),20)
    delta=Q(rng.randint(0,10),100)
    if alpha<=delta:continue
    m=Q(rng.randint(1,30),1); L=Q(rng.randint(0,20),1)
    if (blocks-1)*(alpha-delta)*m*m < L*m*m:
        assert blocks < 1 + L/(alpha-delta)
        checks['greedy_block_cases']+=1
print(json.dumps({'status':'finite_numeric_only_not_lean_kernel','checks':checks},indent=2))
