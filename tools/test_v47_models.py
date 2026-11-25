#!/usr/bin/env python3
"""Exact rational models for the measured-average transfer and anchor rule.
These tests are not Lean kernel checks."""
from fractions import Fraction as F
from random import Random

rng = Random(47086)
for _ in range(500):
    depth = rng.randrange(1, 7)
    n = 2**depth
    # Multiple weighted input values in each terminal cell; leaf means are
    # not point samples. Equal cell lengths model a real dyadic interval.
    data = [[(F(k, 12), F(rng.randrange(0, 31), 7)) for k in (2, 3, 7)] for i in range(n)]
    w = [sum(t for t, x in a) for a in data]
    means = [sum(t*x for t,x in a)/ww for a,ww in zip(data,w)]
    input_energy = sum(t*x*x for a in data for t,x in a)
    assert sum(t*x*x for t,x in zip(w, means)) <= input_energy
    M, S = F(0), F(0)
    for q in range(n):
        a = []
        for j in range(depth+1):
            size = 2**(depth-j)
            l = q//size*size
            ids = range(l,l+size)
            mean = sum(w[i]*means[i] for i in ids)/sum(w[i] for i in ids)
            direct = sum(t*x for i in ids for t,x in data[i])/sum(t for i in ids for t,x in data[i])
            assert mean == direct
            a.append(mean)
        roots = [a[0]]
        for x in a[1:]:
            if x > 2*roots[-1]: roots.append(x)
        m = max(a)
        s = sum(x*x for x in roots)
        assert s <= F(4,3)*m*m
        M += w[q]*m*m
        S += w[q]*s
    assert M <= 4*input_energy
    assert S <= F(16,3)*input_energy
for _ in range(500):
    c = [F(rng.randrange(-20,21), 7) for j in range(rng.randrange(1,70))]
    b = F(rng.randrange(0,15),7)
    anchors = [0]
    for j in range(1,len(c)):
        if abs(c[j]-c[anchors[-1]]) > b: anchors.append(j)
        assert abs(c[j]-c[anchors[-1]]) <= b
    assert all(i<j and abs(c[j]-c[i])>b for i,j in zip(anchors,anchors[1:]))
print('PASS: 500 measured partition and stopping models; 500 exact anchor-path models')
