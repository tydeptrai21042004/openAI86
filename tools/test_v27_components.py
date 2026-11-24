#!/usr/bin/env python3
"""Exact model regressions; not a Lean or full-paper proof certificate."""
from fractions import Fraction as Q
from itertools import permutations, product
from random import Random
rng = Random(27086)
counts = {}
def check(group, condition):
    assert condition, group
    counts[group] = counts.get(group, 0) + 1

def vec(): return [Q(rng.randint(-8,8),rng.randint(1,6)) for _ in range(3)]
def add(a,b): return [x+y for x,y in zip(a,b)]
for _ in range(1000):
    mat=[vec() for _ in range(3)]
    C=lambda u,v: sum(u[i]*mat[i][j]*v[j] for i in range(3) for j in range(3))
    A=lambda u,v:C(u,v)-C(v,u)
    m,mp,d,dp=vec(),vec(),vec(),vec()
    u,up=add(m,d),add(mp,dp)
    check('return antisymmetry', C(up,u)-A(up,m)-C(u,up)+A(u,mp)==A(dp,d)-A(mp,m))
for p,q,e in product(range(-2,3),repeat=3):
    z=Q(e-p+q,8)
    if z.denominator==1:
        check('integer obstruction',z==0)
for _ in range(1000):
    a,b,c=([Q(rng.randint(-9,9),rng.randint(1,7)) for _ in range(8)] for _ in range(3))
    d=max(map(abs,c)); A=sum(x*x for x in a); B=sum(x*x for x in b)
    check('row energy',sum(abs(x*y*z) for x,y,z in zip(a,b,c))**2<=d*d*A*B)
    w=Q(rng.randint(1,9),rng.randint(1,9)); z=w*a[0]+b[0]
    check('clump extraction',abs(a[0])<=(abs(z)+abs(b[0]))/w)
for _ in range(1000):
    n=rng.randrange(20); B=rng.randrange(20); r=Q(rng.randrange(10),10); C=Q(rng.randrange(10))
    check('predictor tail',sum(C*r**(B+j) for j in range(n))<=C*r**B/(1-r))
    fs=[set(rng.randrange(20) for _ in range(rng.randrange(8))) for _ in range(rng.randrange(8))]
    check('predictor catalog',len(set().union(*fs))<=len(fs)*max(map(len,fs),default=0))
for _ in range(1000):
    w=[Q(rng.randrange(-9,10)) for _ in range(7)]; w.append(-sum(w)); f=vec()*3; f=f[:8]
    c=Q(rng.randrange(-9,10)); M=max(map(abs,w)); eps=max(abs(x-c) for x in f)
    check('zero marginal model',abs(sum(x*y for x,y in zip(w,f)))<=8*M*eps)
    x,t,lam=vec()
    check('quadratic cancellation', -lam*x*x+3*lam*(x+t)**2-3*lam*(x+2*t)**2+lam*(x+3*t)**2==0)
    l=rng.randrange(4); n0,n1,nl=[rng.randrange(-15,16) for _ in range(3)]
    check('integer carry',(x+l*t-nl)-((1-l)*(x-n0)+l*(x+t-n1))==(1-l)*n0+l*n1-nl)
    vals=[Q(rng.randrange(-99,100)) for _ in range(8)]
    check('filter insertion telescope',abs(vals[-1]-vals[0])<=sum(abs(y-x) for x,y in zip(vals,vals[1:])))
    q=Q(rng.randrange(-10,11)); x=Q(rng.randrange(-10,11)); h=Q(rng.randrange(-10,11))
    check('linear split',h*x==h*(q*x)+h*(x-q*x))
    V,Qeff=vec()[:2]; H=max(abs(V),abs(Qeff))
    check('dyadic witness',abs(V/2)<=H and abs(Qeff/4)<=H)
weights=[-1,3,-3,1]
for i,j,a,b in permutations(range(4)):
    k=lambda l:weights[l]*Q(b-l,b-a)*Q(l-a,b-a)
    check('mixed curvature',k(i)==-k(j) and k(i)!=0)
# Exact discrete U3 raw cube for L=1,2. Nonzero support makes enumeration cheap:
# x and each x+h_i must belong to [0,L); only L^4 candidates can contribute.
for L in (1,2,3):
    N=16*L
    for f in product((-1,0,1),repeat=L):
        def raw(f):
            res=0
            for x,*y in product(range(L),repeat=4):
                term=1
                for bits in product((0,1),repeat=3):
                    idx=(x+sum((y[i]-x)*bits[i] for i in range(3)))%N
                    term*=f[idx] if idx<L else 0
                res+=term
            return Q(res,N**4)
        den=raw([1]*L); num=raw(f)
        check('interval cube normalization',den>0 and 0<=num<=den)
for key,n in counts.items(): print(f'{key}: {n} PASS')
print(f'V27 TOTAL: {sum(counts.values())} exact model checks PASS')
