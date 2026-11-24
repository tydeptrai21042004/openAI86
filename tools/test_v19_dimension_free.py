#!/usr/bin/env python3
"""Exact rational model checks of V19 identities; not Lean elaboration."""
from fractions import Fraction as Q
from random import Random
from test_v15_actual_projection_blocks import pmat, mv, e, sub
from itertools import product
rng=Random(190086)
counts={}
def ck(name,ok):
    assert ok,name
    counts[name]=counts.get(name,0)+1

def add(x,y): return tuple(a+b for a,b in zip(x,y))
def dif(x,y): return tuple(a-b for a,b in zip(x,y))
def blocks(k,s,n):
    if k==0: return [(s,1)] if n else []
    if n==2**k:return [(s,n)]
    h=2**(k-1)
    return blocks(k-1,s,n) if n<=h else [(s,h)]+blocks(k-1,s+h,n-h)
def aug(i,n,T,x):return mv(pmat(i%4,min(n-1,T)),x) if n else tuple(Q(0) for _ in x)
def energy(xs): return sum(e(x) for x in xs)
def apply(m,n,T,x):
    for i in range(m):x=aug(i,n,T,x)
    return x
for k in range(8):
    for n in range(2**k+1):
        f=[tuple(Q(rng.randrange(-10,11),rng.randrange(1,8)) for _ in range(3)) for j in range(2**k+1)]
        g=blocks(k,0,n)
        v=(Q(0),)*3
        for s,w in g:v=add(v,dif(f[s+w],f[s]))
        ck('additive vector prefix',v==dif(f[n],f[0]))
        ck('unique widths',len({w for s,w in g})==len(g))
        ck('aligned grid',all(s%w==0 and s+w<=n for s,w in g))
for _ in range(100):
    k=rng.randrange(0,5);T=rng.randrange(2**k)
    # Complexification: separate exact rational real/imaginary parts.
    xs=[tuple(Q(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(3)) for j in range(2)]
    ns=[rng.randrange(T+1) for _ in range(2)]
    # two rows with different output dimensions: coordinates 0 and (1,2)
    for m in range(7):
        vals=[[apply(m,n+1,T,x) for x in xs] for n in range(T+1)]
        ev=sum(v[0]**2 for v in vals[ns[0]])+sum(v[j]**2 for v in vals[ns[1]] for j in (1,2))
        ck('complex heterogeneous prefix',ev<=(k+1)**(2*m)*energy(xs))
        if m:
            vv=sum(e(dif(vals[n+1][j],vals[n][j])) for n in range(T) for j in range(2))
            ck('complex variation',vv<=m*m*(k+1)**(2*(m-1))*energy(xs))
    for i in range(4):
        for a in range(T+3):
            for b in range(a,T+3):
                for x in xs:
                    u,v=aug(i,a,T,x),aug(i,b,T,x)
                    ck('augmented nested Pythagoras',e(dif(v,u))==e(v)-e(u))
for _ in range(1200):
    c=[Q(rng.randrange(-8,9),rng.randrange(1,9)) for i in range(5)]
    d=Q(rng.randrange(0,12),11)
    v=[d*Q(rng.randrange(-10,11),10) for i in c]
    M=sum(map(abs,c)); x=sum(a*b for a,b in zip(c,v))
    ck('tiny span bound',abs(x)<=M*d)
    A=M*d+1
    if abs(x)<=d or abs(x)>=A:ck('tiny gap closure',abs(x)<=d)
    p,t,s=[tuple(Q(rng.randrange(-10,11),rng.randrange(1,9)) for j in range(3)) for i in range(3)]
    C=Q(rng.randrange(0,8),3); floor=Q(1,5)
    # l1 norm is a rational upper bound for the Euclidean leakage.
    eps=sum(map(abs,dif(t,p)))
    sigma=C*e(dif(t,s))+floor
    ck('component comparison',sigma<=4*C*e(p)+2*C*e(s)+4*C*eps**2+floor)
print(counts)
print('V19 exact model checks:',sum(counts.values()))
