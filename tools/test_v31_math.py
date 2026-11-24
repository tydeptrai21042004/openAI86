#!/usr/bin/env python3
"""Exact integer/rational regression tests; no kernel verification."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from random import Random
C=Counter()
def check(name, condition):
    if not condition: raise AssertionError(name)
    C[name]+=1
for L in range(1,1001):
    a=set(range(-L,1)); b=set(range(2*L,3*L+1))
    check('disjoint scale windows', not a&b)
    check('exact 2L+2 scales',len(a|b)==2*L+2)
    # Since n<=v<=n+L is the logarithmic form of the actual dyadic annulus.
    check('scale membership',all(0<=-n<=L or 0<=3*L-n<=L for n in a|b))
for K in range(1001):
    L=K+1
    check('no fixed additive repair',2*L+2>K+L+1)
for L in range(1,301):
    count=L+sum((L-s)*(4*s*s+2) for s in range(1,L))
    check('exact cube count formula',3*count==L**4+2*L**2)
    D=Q(count,(16*L)**4)
    check('strong uniform lower bound',D>=Q(1,3*16**4))
    k=(L+3)//4
    check('positive short box',4*(k-1)<L and 4*k>=L)
    check('box mass lower bound',count>=k**4 and Q(k**4,(16*L)**4)>=Q(1,64**4))
for L in range(1,17):
    count=0
    for a,b,c in product(range(-L+1,L),repeat=3):
        count+=max(0,L-abs(a)-abs(b)-abs(c))
    check('direct signed-edge enumeration',3*count==L**4+2*L**2)
for L in range(1,10):
    # Independent enumeration by the four adjacent vertices (actual cyclic cubes).
    N=16*L
    count=0
    for x,y,z,t in product(range(L),repeat=4):
        a,b,c=y-x,z-x,t-x
        if all((x+i*a+j*b+k*c)%N<L for i,j,k in product((0,1),repeat=3)):
            count+=1
    check('cyclic cube enumeration',3*count==L**4+2*L**2)
r=Random(31086)
for _ in range(3000):
    d=r.randrange(1,15); W=r.randrange(0,15); U=r.randrange(0,30)
    points=set()
    for i in range(d):
        a=Q(r.randrange(-1000,1000),4)
        b=a+Q(r.randrange(0,4*(W+U)+1),4)
        points.update(range(-(-a.numerator//a.denominator),b.numerator//b.denominator+1))
    check('corrected packet cover count',len(points)<=d*(W+U+1))
for _ in range(3000):
    values=[Q(r.randrange(0,101),100) for i in range(r.randrange(1,40))]
    eta=sum(values)/len(values)
    p=Q(sum(v>=eta/2 for v in values),len(values))
    check('good derivative density',p>=eta/(2-eta))
for name,n in sorted(C.items()): print(f'{name}: {n} PASS')
print(f'TOTAL: {sum(C.values())} PASS (exact model tests, not formal proofs)')
