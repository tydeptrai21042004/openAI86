#!/usr/bin/env python3
"""Exact mathematical regression models. Not Lean elaboration or proof tests."""
from fractions import Fraction as Q
from itertools import product
from random import Random
from collections import Counter
r=Random(28086); counts=Counter()
def check(name,b):
    assert b,name
    counts[name]+=1
# Gaussian integers represented as pairs, with no floating-point operations.
def add(z,w): return z[0]+w[0],z[1]+w[1]
def mul(z,w): return z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0]
def conj(z): return z[0],-z[1]
def prod(zs):
    a=(1,0)
    for z in zs:a=mul(a,z)
    return a
def total(zs):
    a=(0,0)
    for z in zs:a=add(a,z)
    return a
def normsq(z):return z[0]**2+z[1]**2
def face(f,a,b,x):
    n=len(f)
    return prod((f[x],conj(f[(x+a)%n]),conj(f[(x+b)%n]),f[(x+a+b)%n]))
for n in range(1,8):
    for _ in range(15):
        f=[(r.randrange(-2,3),r.randrange(-2,3)) for i in range(n)]
        raw=(0,0)
        for x,a,b,c in product(range(n),repeat=4):
            term=prod(conj(f[(x+u*a+v*b+w*c)%n]) if (u+v+w)%2 else f[(x+u*a+v*b+w*c)%n] for u,v,w in product(range(2),repeat=3))
            check('eight-vertex factor',term==mul(face(f,a,b,x),conj(face(f,a,b,(x+c)%n))))
            raw=add(raw,term)
        e=sum(normsq(total(face(f,a,b,x) for x in range(n))) for a,b in product(range(n),repeat=2))
        check('cube energy and positivity',raw==(e,0) and e>=0)
for L in range(1,16):
    N=16*L
    # Count supported cubes via the four vertices x,x+h1,x+h2,x+h3.
    num=0
    for x,y,z,w in product(range(L),repeat=4):
        v=[(x+u*(y-x)+v*(z-x)+s*(w-x))%N for u,v,s in product(range(2),repeat=3)]
        num+=all(i<L for i in v)
    check('interval normalization denominator',num>=L*L)
for _ in range(1200):
    m=r.randrange(2,30); n=r.randrange(1,m); z=(m*m-n*n,2*m*n); mod=m*m+n*n
    s=(Q(z[0],mod),Q(-z[1],mod))
    check('exact dual test phase',normsq(s)==1 and mul(s,z)==(mod,0))
    t=Q(r.choice([-1,1])*r.randrange(1,15),r.randrange(1,10)); A=Q(r.randrange(1,10),r.randrange(1,10)); B=A+Q(r.randrange(0,15),r.randrange(1,10)); k=r.randrange(1,8)
    # For psi(s)=s^k, integrate k*t^(k-1)*a^(-k-1) exactly.
    integral=t**(k-1)*(A**(-k)-B**(-k))
    check('positive-window scale reconstruction',integral==((t/A)**k-(t/B)**k)/t)
for key,value in counts.items(): print(f'{key}: {value} PASS')
print(f'V28 TOTAL: {sum(counts.values())} exact model checks PASS')
