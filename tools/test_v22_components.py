#!/usr/bin/env python3
"""Exact regression models for V22, independent of Lean elaboration."""
from fractions import Fraction as F
from itertools import permutations
from math import prod, factorial, gcd, floor
from random import Random
from collections import Counter
rng=Random(86022)
counts=Counter()
def check(k,c):
    if not c: raise AssertionError(k)
    counts[k]+=1

def det(A):
    n=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*prod(A[i][p[i]] for i in range(n)) for p in permutations(range(n)))

def rank(A):
    B=[list(map(F,row)) for row in A]
    if not B:return 0
    r=0
    for j in range(len(B[0])):
        p=next((i for i in range(r,len(B)) if B[i][j]),None)
        if p is None:continue
        B[r],B[p]=B[p],B[r]
        v=B[r][j]; B[r]=[x/v for x in B[r]]
        for i in range(r+1,len(B)):
            v=B[i][j]; B[i]=[a-v*b for a,b in zip(B[i],B[r])]
        r+=1
        if r==len(B):break
    return r

def row_basis(A):
    out=[]
    for i,row in enumerate(A):
        if rank([A[j] for j in out]+[row])>len(out):out.append(i)
    return out

def egcd(a,b):
    if b==0:return a,1,0
    g,x,y=egcd(b,a%b)
    return g,y,x-(a//b)*y

for _ in range(1200):
    d=rng.randint(1,7); k=rng.randint(1,min(4,d)); H=rng.randint(1,9)
    A=[[rng.randint(-H,H) for _ in range(k)] for _ in range(d)]
    sel=row_basis(A); check('basis_rank',len(sel)==rank(A)); check('basis_indices',len(set(sel))==len(sel))
    if len(sel)==k:
        M=[A[i] for i in sel]; D=det(M); check('selected_minor',D!=0)
        b=[rng.randint(-H,H) for _ in range(k)]; c=[]
        for j in range(k):
            Q=[[b[i] if t==j else M[i][t] for t in range(k)] for i in range(k)]
            num=det(Q);check('cramer_numerator',abs(num)<=factorial(k)*H**k);c.append(F(num,D))
        check('cramer_system',all(sum(a*x for a,x in zip(row,c))==bi for row,bi in zip(M,b)))
        check('cramer_l1',sum(map(abs,c))<=k*factorial(k)*H**k)

for _ in range(1800):
    d=rng.randint(1,9); L=rng.randint(1,100); q=rng.randint(1,100)
    g,u,v=egcd(q,L)
    if g!=1:continue
    # U = kernel of first coordinate. Build a,b satisfying q a - L b ∈ U.
    t=rng.randint(-30,30); a=[L*t]+[rng.randint(-100,100) for _ in range(d-1)]
    b=[q*t]+[rng.randint(-100,100) for _ in range(d-1)]
    c=[u*bi+v*ai for ai,bi in zip(a,b)]
    check('bezout_coset',a[0]-L*c[0]==0)
    k=rng.randint(1,8); B=rng.randint(1,12); w=[[rng.randint(-B,B) for _ in range(d)] for _ in range(k)]
    t=[F(rng.randint(-100,100),rng.randint(1,20)) for _ in range(k)]
    target=[F(ai)-sum(tj*wj[i] for tj,wj in zip(t,w)) for i,ai in enumerate(a)]
    rounded=[ai-sum(floor(tj)*wj[i] for tj,wj in zip(t,w)) for i,ai in enumerate(a)]
    for i in range(d):
        check('rounded_bound',abs(rounded[i]-target[i])<=k*B)
        check('rounded_coset',a[i]-rounded[i]==sum(floor(tj)*wj[i] for tj,wj in zip(t,w)))

for _ in range(1200):
    n=rng.randint(1,12); m=rng.randint(1,8); X=range(n)
    C=[{x for x in X if rng.random()<.5} for _ in range(m)]
    D=[{x for x in X if rng.random()<.5} for _ in range(m)]
    a=[F(rng.randint(-20,20),rng.randint(1,9)) for _ in range(m)]
    b=[F(rng.randint(-20,20),rng.randint(1,9)) for _ in range(m)]
    for x in X:
        av=sum(ai for ci,ai in zip(C,a) if x in ci); bv=sum(bi for di,bi in zip(D,b) if x in di)
        check('combined_endpoint_product',av*bv==sum(ai*bi for ci,ai in zip(C,a) for di,bi in zip(D,b) if x in ci&di))
    # Test private-coordinate inequality using positive inverse weights.
    W=rng.randint(1,10); w=[F(rng.randint(1,10),W) for _ in a]
    check('private_combined',sum(ai**2 for ai in a)<=W**2*sum((wi*ai)**2 for wi,ai in zip(w,a)))
    N=[sum(x in ci for ci in C) for x in X]; threshold=rng.randint(1,m)
    check('top_markov',threshold*sum(v>=threshold for v in N)<=sum(N))
    sigma=F(rng.randint(1,15),rng.randint(1,7)); eps=sigma**2/F(rng.randint(2,8)); mass=F(rng.randint(0,50),7); budget=(sigma**2-eps)*mass
    check('top_absorption',sigma**2*mass<=2*budget)

for _ in range(1600):
    l,g,s,x,y=[F(rng.randint(-30,30),rng.randint(1,9)) for _ in range(5)]; R=abs(x-y)+F(rng.randint(0,10),7)
    f=lambda t:2*l*t+g+s
    check('affine_variation',abs(f(x)-f(y))<=2*abs(l)*R)
    A=4*abs(l)*R
    if abs(f(y))>A:check('uniform_derivative_lower',abs(f(x))>A/2)
    n=rng.randint(1,8); a=[F(rng.randint(-12,12),rng.randint(1,7)) for _ in range(n)]; q=[F(rng.randint(-12,12),rng.randint(1,7)) for _ in range(n)]
    delta=max(map(abs,q)); E=sum(ai**2 for ai in a)
    check('lift_physical',sum(ai*qi for ai,qi in zip(a,q))**2<=n*delta**2*E)
    # Local L² refits on piecewise constant vectors, weighted atomic measures.
    weights=[F(rng.randint(1,10),rng.randint(1,9)) for _ in a]
    mean=sum(w*ai for w,ai in zip(weights,a))/sum(weights)
    check('L2_refit_moment',sum(w*(ai-mean) for w,ai in zip(weights,a))==0)
    check('L2_refit_energy',sum(w*mean**2 for w in weights)==sum(w*ai*mean for w,ai in zip(weights,a)))

for k,v in sorted(counts.items()):print(f'{k}: {v}')
print(f'V22 exact arithmetic/model checks: {sum(counts.values())} PASS')
