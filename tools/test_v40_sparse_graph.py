#!/usr/bin/env python3
"""Exact finite regression checks, NOT a Lean proof or sparse theorem test."""
from fractions import Fraction as F
from itertools import product

M = 3
checked = 0
for bits in product((0,1), repeat=M*M):
    if not any(bits):
        continue
    a = lambda u,v: bits[u*M+v]
    eta = F(sum(bits), M*M)
    t = eta**2*M/1600
    c = lambda u,w: sum(a(u,v)*a(w,v) for v in range(M))
    Y = None
    for v in range(M):
        y = [u for u in range(M) if a(u,v)]
        bad = sum(c(u,w)<t for u in y for w in y)
        if len(y)**2-100*bad >= eta**2*M**2/8:
            Y = y
            assert F(bad) <= F(len(y)**2,100)
            break
    assert Y is not None
    B = [u for u in Y if sum(c(u,w)<t for w in Y)<=F(len(Y),4)]
    assert len(B)>=eta*M/5
    # A restricted Latin-square edge coloring is proper on this graph.
    color = lambda u,v: (u+v)%M
    for u,w in product(B, repeat=2):
        paths=[(z,v,t_) for z,v,t_ in product(range(M),repeat=3)
               if a(u,v) and a(z,v) and a(z,t_) and a(w,t_)]
        codes={(color(u,v),color(z,v),color(z,t_),color(w,t_)) for z,v,t_ in paths}
        assert len(paths)==sum(c(u,z)*c(z,w) for z in range(M))
        assert len(paths)==len(codes)
        assert len(codes)>=eta**5*M**3/(8*1600**2)
    checked+=1
print(f'PASS: {checked} nonempty 3x3 adjacency matrices; exact graph/colored-walk regression only')
