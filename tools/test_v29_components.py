#!/usr/bin/env python3
"""Exact rational/integer regression models; not kernel certification."""
from fractions import Fraction as Q
from random import Random
from collections import Counter
r=Random(29086); counts=Counter()
def check(name, condition):
    assert condition, name
    counts[name]+=1
# Random rooted attempt trees. Local contraction is imposed only per parent.
for _ in range(400):
    rho=Q(r.randrange(0,9),10); A=Q(r.randrange(1,12),3)
    root=Q(r.randrange(1,30),7); levels=[[root]]
    for depth in range(5):
        children=[]
        for p in levels[-1]:
            n=r.randrange(4); weights=[r.randrange(1,8) for _ in range(n)]
            cs=[p*rho*Q(w,sum(weights)+1) for w in weights]
            check('local children',sum(cs)<=rho*p)
            children.extend(cs)
        levels.append(children)
    for n in range(5): check('generation contraction',sum(levels[n+1])<=rho*sum(levels[n]))
    mass=sum(map(sum,levels)); cost=sum(A*m for L in levels for m in L)
    check('root packing',mass<=root/(1-rho))
    check('cost packing',cost<=A*root/(1-rho))
# Integer-coordinate two-step group with arbitrary bilinear form on Z^2.
for _ in range(1500):
    C=[[r.randrange(-4,5) for _ in range(2)] for _ in range(2)]
    def B(x,y):return sum(x[i]*C[i][j]*y[j] for i in range(2) for j in range(2))
    def mul(a,b):return (a[0]+b[0],a[1]+b[1],a[2]+b[2]+B(a[:2],b[:2]))
    def inv(a):return (-a[0],-a[1],-a[2]+B(a[:2],a[:2]))
    a,b,c=[tuple(r.randrange(-10,11) for _ in range(3)) for _ in range(3)]
    check('group associativity',mul(mul(a,b),c)==mul(a,mul(b,c)))
    check('group inverse',mul(a,inv(a))==mul(inv(a),a)==(0,0,0))
    comm=mul(mul(mul(a,b),inv(a)),inv(b))
    check('central commutator',comm[:2]==(0,0) and mul(comm,c)==mul(c,comm))
    # Even horizontal and even central coordinates form a subgroup.
    x,y=[tuple(2*r.randrange(-8,9) for _ in range(3)) for _ in range(2)]
    check('integer subgroup',all(z%2==0 for z in mul(x,y)+inv(x)))
    ax=mul(a,x); axy=mul(ax,y)
    check('coset transitivity',all(z%2==0 for z in mul(inv(a),axy)))
# Dominance obstruction for arbitrary signed bounded integer coefficients.
for _ in range(3000):
    k=r.randrange(0,15); H=r.randrange(1,10); M=Q(r.randrange(1,20),5)
    aa=[r.randrange(-H,H+1) for _ in range(k)]
    vv=[M*Q(r.randrange(-10,11),10) for _ in range(k)]
    a=r.choice([j for j in range(-H,H+1) if j]); v=r.choice([-1,1])*(k*H*M+Q(1,7))
    check('dominant relation',sum(x*y for x,y in zip(aa,vv))+a*v!=0)
for k,v in sorted(counts.items()):print(f'{k}: {v} PASS')
print(f'TOTAL: {sum(counts.values())} PASS (model tests only)')
