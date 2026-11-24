#!/usr/bin/env python3
"""Exact model regressions for V23. These are not Lean certificates."""
from fractions import Fraction as F
from itertools import product
from math import gcd, factorial
from random import Random
r = Random(23086)
counts = {}
def check(name, condition):
    assert condition, name
    counts[name] = counts.get(name, 0) + 1

# Exact weighted restrictions, disjoint support, and moment preservation.
for _ in range(1000):
    n=r.randrange(1,21); cells=[r.randrange(4) for _ in range(n)]
    w=[F(r.randrange(1,6),7) for _ in range(n)]
    x=[F(r.randrange(-10,11),3) for _ in range(n)]
    y=[F(r.randrange(-10,11),5) for _ in range(n)]
    restrict=lambda z,j:[v if c==j else 0 for c,v in zip(cells,z)]
    dot=lambda u,v:sum(t*a*b for t,a,b in zip(w,u,v))
    for a,b in product(range(4),repeat=2):
        if a!=b: check('disjoint restrictions',dot(restrict(x,a),restrict(y,b))==0)
    check('restriction assembly',sum(dot(restrict(x,j),restrict(y,j)) for j in range(4))==dot(x,y))

# Nonuniform column denominators: coefficient rescaling must include q/Q.
for _ in range(2000):
    a,b,c,d=[r.randrange(-8,9) for _ in range(4)]
    det=a*d-b*c
    if not det: continue
    u,v=[r.randrange(-8,9) for _ in range(2)]
    x,y=F(d*u-b*v,det),F(a*v-c*u,det)
    q1,q2,Q=[r.randrange(1,13) for _ in range(3)]
    M=max(q1,q2); H=max(map(abs,(a,b,c,d,u,v)))
    t,s=F(q1,Q)*x,F(q2,Q)*y
    check('rescaled Cramer',abs(t)+abs(s)<=M*2*factorial(2)*H**2)
    check('original rational system',F(a,q1)*t+F(b,q2)*s==F(u,Q) and F(c,q1)*t+F(d,q2)*s==F(v,Q))

# Rational quotient represented by projection onto last coordinate;
# first coordinate is a rational subspace. gcd witness computed exactly.
def egcd(a,b):
    if b==0:return a,1,0
    g,u,v=egcd(b,a%b);return g,v,u-(a//b)*v
for q,L,R in product(range(1,25),range(1,25),range(1,7)):
    if gcd(q,L)!=1:continue
    d=r.randrange(1,20); k=r.randrange(-12,13)
    a=(r.randrange(-20,21),L*R*k);b=(r.randrange(-20,21),q*k)
    g,u,v=egcd(q,L); z=tuple(u*bi*R+v*ai for ai,bi in zip(a,b))
    check('quotient lift',a[1]-L*z[1]==0 and g==1 and d*q*a[1]-d*L*R*b[1]==0)

# Dyadic first tops and overlap on a last-separating grid.
for _ in range(1000):
    T=6; size=2**T
    label=lambda n,x:x//(2**(T-n))
    used={(n,j) for n in range(T+1) for j in range(2**n) if r.random()<0.12}
    x=r.randrange(size); ts=[n for n in range(T+1) if (n,label(n,x)) in used]
    if ts:
        t=min(ts)
        for y in range(size):
            if label(t,x)==label(t,y):
                check('first top whole cell',min(n for n in range(T+1) if (n,label(n,y)) in used)==t)
    d=r.randrange(T+1);a=r.randrange(d+1);b=r.randrange(d+1)
    y=label(d,x)*2**(T-d)+r.randrange(2**(T-d))
    check('grid constancy',label(a,x)==label(a,y) and label(b,x)==label(b,y))

# Two frequency equations and exact exponent algebra from Section 9.
for _ in range(3000):
    a,b=r.sample(range(4),2);x,y=[F(r.randrange(-50,51),13) for _ in range(2)]
    Q=x+y;T=a*x+b*y;E=max(abs(Q),abs(T))
    check('pair determination',abs(x)<=4*E and abs(y)<=4*E)
    p0=F(r.randrange(1,100),100);theta=F(r.randrange(1,25),100)
    p=1-theta+theta*p0;e=[p-2*(1-theta),p-2*(1-theta),p,p-4*theta*p0]
    check('amplitude powers',sum(e)==0 and all(sum(e[:i])<0 for i in (1,2,3)) and p>F(2,3))
    # first-derivative correction budget (scalar inequalities only)
    A=F(r.randrange(1,25),7);length=F(r.randrange(1,25),7);K=A/length*F(r.randrange(0,11),10)
    check('oscillatory budget',2/A+K/A**2*length<=3/A)
    # separate mode coordinates, test exact contraction for weights with sum squares <= 1
    f=[F(r.randrange(-10,11),3) for _ in range(4)]
    weights=[[F(r.randrange(-2,3),4) for _ in range(4)] for _ in f]
    check('private lift',sum((u*v)**2 for u,row in zip(f,weights) for v in row)<=sum(u*u for u in f))
for key,n in counts.items():print(f'{key}: {n} PASS')
print(f'TOTAL V23 MODEL ASSERTIONS: {sum(counts.values())}')
