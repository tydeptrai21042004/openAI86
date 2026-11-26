#!/usr/bin/env python3
"""Exact model sanity checks, NOT tests of Lean proofs."""
from fractions import Fraction as F
from random import Random
from itertools import product
rng=Random(560086)
# 3.2: weighted complex scalar represented as integer pairs.
for _ in range(300):
    n=rng.randrange(1,7); D=max(2,n+2)
    a=[F(rng.randrange(1,D+1),D) for i in range(n)]
    phi=[(rng.randrange(-1,2),rng.randrange(-1,2)) for i in range(n)]
    c=[(rng.randrange(-3,4),rng.randrange(-3,4)) for i in range(n)]
    norm2=lambda z: z[0]**2+z[1]**2
    assert all(norm2(p)+w*w<=D*D for p,w in zip(phi,a))
    sr=sum(p[0]*u[0]-p[1]*u[1] for p,u in zip(phi,c))
    si=sum(p[0]*u[1]+p[1]*u[0] for p,u in zip(phi,c))
    C=sum(map(norm2,c)); E=sr*sr+si*si+sum(w*w*norm2(u) for w,u in zip(a,c))
    assert F(C,D*D)<=E<=D**3*C
# 8.2: exact translated packet windows, K-spaced starts and witnesses.
for _ in range(500):
    d=rng.randrange(1,8); K=F(rng.randrange(4,31)); tau=K/8; W=K-2*tau
    b0=F(rng.randrange(-100,101),3); P=[F(rng.randrange(-100,101),2) for _ in range(d)]
    S=set()
    for p in P:
        for n in range(-100,101):
            b=b0+K*n
            if b-2*K-tau < p+W/2 and p-W/2 < b+K+tau:S.add(n)
    assert len(S)<=5*len(P)
# 8.5: arbitrary nested sets, actual incidences, ties and zero new labels.
for _ in range(500):
    M=rng.randrange(1,15); T=rng.randrange(1,15); A=rng.randrange(1,6)
    entry=[rng.randrange(T) for _ in range(M)]
    used=[0]*M; cost=F(0)
    for t in range(T):
        S=[r for r,e in enumerate(entry) if e<=t]
        X=[r for r in S if used[r]<A and rng.randrange(2)]
        for r in X:used[r]+=1
        if S:cost+=F(len(X),len(S))
    assert cost<=A*sum(F(1,r) for r in range(1,M+1))
print('V56 exact model sanity checks: 1300/1300 passed (not Lean kernel checks)')
