#!/usr/bin/env python3
"""Exact rational models of V57 proof steps, not Lean kernel tests."""
from fractions import Fraction as F
from itertools import product
from math import factorial
from random import Random
import json
rng=Random(57)
# Enumerate all height-H vectors, using exact reduced rationals. Tiny
# generators can have a nonzero evaluation; the gap excludes intermediates.
counts={'tiny_span':0,'bad_density_chain':0,'tuple_cutoff':0}
for H in (1,2,3):
    V=sorted({F(p,q) for p in range(-H,H+1) for q in range(1,H+1)})
    for _ in range(60):
        d=2; eps=F(H); reserve=d*factorial(d)*H**(d*d+d)*eps
        lam=reserve+1
        theta=(F(rng.choice([-1,0,1])),F(H*(lam+H+1)))
        vals={a:abs(sum(x*y for x,y in zip(a,theta))) for a in product(V,repeat=2)}
        assert all(v<=eps or v>=lam for v in vals.values())
        tiny=[a for a,v in vals.items() if v<=eps]
        nonzero=next((a for a in tiny if a!=(0,0)),None)
        if nonzero is not None:
            rank2=any(nonzero[0]*a[1]!=nonzero[1]*a[0] for a in tiny)
            for a,v in vals.items():
                if rank2 or nonzero[0]*a[1]==nonzero[1]*a[0]: assert v<=eps
        else: assert vals[(0,0)]==0
        counts['tiny_span']+=1

def rank(n):
    k=0; x=F(1)
    while x*F(11,10)<=n: x*=F(11,10); k+=1
    return k
for _ in range(500):
    N=rng.randint(1,8); H=rng.randint(1,18); M=rng.randint(1,25); lag=rng.randint(1,5)
    beta=F(rng.randint(1,4),5); delta=F(rng.randint(1,4),5)
    # Each label enters at a position (P or C) and a height. This creates
    # nesting in both directions, including the last P subset C.
    entries=[(rng.randrange(2*N),rng.randrange(H)) for _ in range(M-1)]
    def labels(i,h): return {0}|{x+1 for x,(t,u) in enumerate(entries) if t<=i and u<=h}
    P=[[labels(2*i,h) for h in range(H)] for i in range(N)]
    C=[[labels(2*i+1,h) for h in range(H)] for i in range(N)]
    X=[{x for x in range(M) if rng.randrange(8)==0} for i in range(N)]
    Y=[[{x for x in range(M) if x not in X[i] and rng.randrange(8)==0} for h in range(H)] for i in range(N)]
    A=max(sum(x in Y[i][h] for h in range(H)) for i in range(N) for x in range(M))
    B=max(sum(x in X[i] for i in range(N)) for x in range(M))
    L=rank(M); hm=sum((F(1,k) for k in range(1,M+1)),F(0)); Q=lag*(L+1)+A*hm/beta; R=L+B*hm/beta
    bad=[]
    for i in range(N):
        row=0
        for h in range(H):
            p=rank(len(P[i][h])); c=rank(len(C[i][h])); p0=rank(len(P[i][max(0,h-lag)]))
            v=F(len((X[i]|Y[i][h])&C[i][h]),len(C[i][h])); b=int(h<lag or p0!=c or v>beta)
            maj=int(h<lag)+p-p0+c-p+F(len(X[i]&C[i][h])+len(Y[i][h]&C[i][h]),len(C[i][h]))/beta
            assert b<=maj; row+=b
        bad.append(row)
        assert sum((F(len(Y[i][h]&C[i][h]),len(C[i][h])) for h in range(H)),F(0))<=A*hm
    for h in range(H): assert sum((F(len(X[i]&C[i][h]),len(C[i][h])) for i in range(N)),F(0))<=B*hm
    assert sum(bad)<=N*Q+H*R
    if all(x>delta*H for x in bad) and 2*Q<=delta*H: assert N<2*R/delta
    counts['bad_density_chain']+=1
for _ in range(500):
    m=rng.randint(1,12); B=rng.randint(1,4); n=rng.randint(0,15); CN=F(rng.randint(0,25),3); R=F(rng.randint(0,10),2)
    w=[F(1,2**(j+1)) for j in range(n)]
    # Sum_{j>=0} (j+m) 2^{-j-1} = m+1.
    cost=F(0)
    for j,wj in enumerate(w):
        for _i in range(rng.randrange(B*(j+m)+1)):
            cost+=F(rng.randrange(11),10)*wj*(1+CN)*R
    assert cost<=B*(m+1)*(1+CN)*R
    counts['tuple_cutoff']+=1
print(json.dumps({'kind':'exact arithmetic models, not Lean certificates','counts':counts,'total':sum(counts.values())},indent=2))
