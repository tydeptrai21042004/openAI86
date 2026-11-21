#!/usr/bin/env python3
"""Finite deterministic tests of two newly stated inequalities.

These are arithmetic tests, not a Lean kernel proof or a verification of
any infinite-dimensional part of the paper.
"""
from fractions import Fraction as F
from random import Random
import json

rng=Random(86021121)
counts={'predictor_energy_cases':0, 'finite_predictor_sums':0,
        'bad_density_incidence_cases':0}

# Square-energy inequality, with exact integer square roots of epsilon.
for root in (0, 1, 2, 3, 5):
    eps=root*root
    for _ in range(500):
        a0,a1,p0,p1=(rng.randint(-10,10) for _ in range(4))
        v=eps*(a1-a0)-root*(p1-p0)
        upper=2*eps**2*(a1-a0)**2+2*eps*(p1-p0)**2
        assert v*v <= upper
        counts['predictor_energy_cases']+=1
    for _ in range(120):
        ys=[tuple(rng.randint(-10,10) for _ in range(4))
            for _ in range(rng.randint(0,40))]
        lhs=sum((eps*(a1-a0)-root*(p1-p0))**2 for a0,a1,p0,p1 in ys)
        rhs=2*eps**2*sum((a1-a0)**2 for a0,a1,p0,p1 in ys)
        rhs+=2*eps*sum((p1-p0)**2 for a0,a1,p0,p1 in ys)
        assert lhs<=rhs
        counts['finite_predictor_sums']+=1

# Lemma 8.6 final incidence step: a finite matrix of height incidences,
# per-position lower bound delta*H and global upper N*Q + H*R.
for n in range(0,12):
    for h in range(1,12):
        for delta in (F(1,5),F(1,3),F(1,2),F(2,3)):
            for _ in range(10):
                matrix=[[rng.randint(0,2) for _ in range(h)] for _ in range(n)]
                row=[sum(z) for z in matrix]
                if any(s < delta*h for s in row): continue
                q=delta*h*F(rng.randint(0,5),10)
                if 2*q > delta*h: continue
                r=(F(sum(row))-n*q)/h
                assert F(sum(row))<= n*q + h*r
                assert n <= 2*r/delta
                counts['bad_density_incidence_cases']+=1

print(json.dumps({'scope':'exact_finite_arithmetic_not_lean',
                  'status':'PASS','checks':counts},indent=2))
