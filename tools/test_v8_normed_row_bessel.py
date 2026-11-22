#!/usr/bin/env python3
"""Exact Gaussian-rational models for V8 normed/noncommuting Bessel bounds.
These are finite counterexample searches, never Lean kernel certificates.
"""
from fractions import Fraction as F
from itertools import product
from random import Random
from math import prod

rng=Random(862026)
checks=0

def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def cadd(a,b): return (a[0]+b[0],a[1]+b[1])
def cscale(a,b): return (a*b[0],a*b[1])
def csq(a): return a[0]*a[0]+a[1]*a[1]
def norm2(x): return sum(csq(y) for y in x)
def matvec(M,x):
    return tuple((sum(M[i][j]*x[j][0] for j in range(2)),
                  sum(M[i][j]*x[j][1] for j in range(2))) for i in range(2))
def dotrow(row,x):
    return (sum(row[j]*x[j][0] for j in range(2)),
            sum(row[j]*x[j][1] for j in range(2)))
def projection(a,b):
    denom=a*a+b*b
    return ((a*a/denom,a*b/denom),(a*b/denom,b*b/denom))
def eye_minus(P):
    return tuple(tuple(F(int(i==j))-P[i][j] for j in range(2)) for i in range(2))

unitpairs=((F(3),F(4)),(F(5),F(12)),(F(8),F(15)),(F(7),F(24)))
rows=((F(3,5),F(4,5)),(F(-4,5),F(3,5)))
blocks=[(projection(*ab),eye_minus(projection(*ab))) for ab in unitpairs]
xs=[((F(a),F(b)),(F(c),F(d))) for a,b,c,d in [
    (1,2,3,-1),(0,-2,5,1),(-3,1,2,-2),(4,-3,-1,1),(1,0,0,1)]]
for m in range(5):
    for x in xs:
        # Each layer is a pair of orthogonal but across-layer noncommuting blocks.
        all_word_energy=F(0)
        for word in product((0,1),repeat=m):
            y=x
            for layer,b in enumerate(word): y=matvec(blocks[layer][b],y)
            all_word_energy += norm2(y)
        assert all_word_energy==norm2(x), ('layer energy',m,x)
        checks+=1
        for encoded in range(1<<(2*m)):
            vals=[]
            for r in range(2):
                y=x
                for layer in range(m):
                    bit=(encoded>>(r*m+layer))&1
                    y=matvec(blocks[layer][bit],y)
                vals.append(dotrow(rows[r],y))
            assert sum(csq(z) for z in vals)<=norm2(x), ('row energy',m,x,encoded)
            checks+=1

# General projection chains preserve energy even if the maps do not commute.
for m in range(6):
    for x in xs:
        y=x
        for j in range(m):
            y=matvec(blocks[j%len(blocks)][0],y)
        assert norm2(y)<=norm2(x)
        assert sum(csq(dotrow(row,y)) for row in rows) <= norm2(x)
        checks+=2

# m=1 square variation for nested projections P_0=0, P_1=rank1, P_2=I.
zero=((F(0),F(0)),(F(0),F(0)))
ident=((F(1),F(0)),(F(0),F(1)))
for x in xs:
    for p,_ in blocks:
        Px=[matvec(M,x) for M in (zero,p,ident,ident,ident)]
        diff=sum(norm2(tuple((Px[i+1][j][0]-Px[i][j][0],
                              Px[i+1][j][1]-Px[i][j][1]) for j in range(2)))
                  for i in range(len(Px)-1))
        assert diff<=norm2(x)
        checks+=1

print(f'V8 exact Gaussian-rational checks: {checks:,} PASS')
