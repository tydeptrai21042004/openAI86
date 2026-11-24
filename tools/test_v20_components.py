#!/usr/bin/env python3
"""Exact arithmetic regressions for V20; not Lean verification."""
from fractions import Fraction as F
from itertools import permutations
from math import factorial
import random
rng=random.Random(86020)
counts={}
def check(group, condition):
    assert condition, group
    counts[group]=counts.get(group,0)+1
# Nat.clog envelope and minimality, including powers and neighboring integers.
for n in list(range(1,4097))+[max(1,2**k+d) for k in range(1,100) for d in (-1,0,1)]:
    k=(n-1).bit_length()
    check('clog_envelope', n<=2**k and (k==0 or 2**(k-1)<n))
# Exact rational model for the moment absorption inequality (S is a square).
for _ in range(3000):
    t=F(rng.randrange(100),rng.randrange(1,20)); B=F(rng.randrange(-100,101),rng.randrange(1,20)); S=t*t
    A=S-B*t+F(rng.randrange(20),7)
    check('moment_absorption', S<=A+B*t and S<=2*A+B*B)
    D=F(rng.randrange(2,100)); Z=F(rng.randrange(1,100),9); l=F(rng.randrange(1,25)); L=l*l
    # Choose a rational S=t² with t= l*Z, always satisfying the premise.
    S=(l*Z)**2
    check('moment_representatives', S<=4*Z*Z/D**2+l*Z*(l*Z) and S<=(8/D**2+L)*Z*Z)
    a=F(rng.randrange(1,10),3); G=F(rng.randrange(1,10),2); cost=F(rng.randrange(1,10),3); V=F(rng.randrange(1,10),4)
    parent=F(rng.randrange(1,40)); E=G*G*a*a*parent*F(rng.randrange(0,11),10)
    mass=V*E/(cost*a*a)*F(rng.randrange(0,11),10); child=G*G*a*a*mass*F(rng.randrange(0,11),10)
    check('anchor_budgets', mass<=V*G*G/cost*parent and child<=V*G*G/cost*E)
# Integer determinant and actual Cramer ratios, using exact permutation expansion.
def det(A):
    k=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(k) for j in range(i+1,k))*prod(A[p[i]][i] for i in range(k)) for p in permutations(range(k)))
def prod(a):
    x=1
    for v in a: x*=v
    return x
for _ in range(1200):
    k=rng.randrange(1,5); H=rng.randrange(1,10); A=[[rng.randrange(-H,H+1) for _ in range(k)] for _ in range(k)]; b=[rng.randrange(-H,H+1) for _ in range(k)]
    d=det(A); M=factorial(k)*H**k
    check('determinant_bound',abs(d)<=M)
    if d:
        nums=[det([[b[i] if j==r else A[i][j] for j in range(k)] for i in range(k)]) for r in range(k)]
        c=[F(n,d) for n in nums]
        check('cramer_solution',all(sum(A[i][j]*c[j] for j in range(k))==b[i] for i in range(k)))
        check('cramer_l1',sum(map(abs,c))<=k*M)
        delta=F(1,100); v=[delta*F(rng.randrange(-10,11),10) for _ in range(k)]; x=sum(ci*vi for ci,vi in zip(c,v)); large=k*M*delta+1
        check('tiny_gap_bound', abs(x)<large)
# Actual exceptional starts in a K-spaced schedule for each log packet.
for _ in range(3000):
    K=rng.randrange(1,30); tau=F(rng.randrange(K+1),2); W=F(K)-2*tau; alpha=F(rng.randrange(-100,100),3)
    starts=[j*K for j in range(-200,201) if alpha-K-tau<j*K<alpha+W+2*K+tau]
    check('packet_exception_count',len(starts)<=5)
# Rank stabilization windows, including lag 0 and empty horizon.
for _ in range(3000):
    H=rng.randrange(0,50); R=rng.randrange(0,15); d=rng.randrange(0,25)
    p=sorted(rng.randrange(d+1) for _ in range(H+R+1)); q=sorted(rng.randrange(d+1) for _ in range(H+R+1))
    check('rank_single',sum(p[i]<p[i+R] for i in range(H))<=R*d)
    check('rank_union',sum(p[i]<p[i+R] or q[i]<q[i+R] for i in range(H))<=2*R*d)
    total=rng.randrange(0,40); b=[F(rng.randrange(-50,51),rng.randrange(1,12)) for _ in range(total)]; s=rng.sample(range(total),rng.randrange(total+1)); D=len(s)+rng.randrange(0,5)
    check('path_synthesis',sum(b[i] for i in s)**2<=D*sum(b[i]**2 for i in s))
print('V20 exact model checks:',sum(counts.values()))
for k,v in counts.items(): print(k,v)
