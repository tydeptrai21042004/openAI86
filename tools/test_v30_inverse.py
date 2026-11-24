#!/usr/bin/env python3
"""Independent exact Gaussian-integer and rational regression checks.
Not a Lean kernel certificate. The support interval is embedded in Z/(16L).
For a supported cube, lifts of the three edges have absolute value < L;
all vertices then lie in (-3L,4L), so testing the integer lifts is exact.
"""
from collections import Counter
from itertools import product
from fractions import Fraction as Q
from random import Random
counts=Counter()
def ck(name,ok):
    assert ok,name
    counts[name]+=1
# Represent Gaussian integers as Python complex values. Here all values and
# intermediate sums are small integers, exactly represented in binary64.
units=(1+0j,-1+0j,1j,-1j)
vertices=list(product((0,1),repeat=3))
def cubes(L):
    for x,a,b,c in product(range(L),repeat=4):
        hs=(a-x,b-x,c-x)
        inds=tuple(x+sum(w*h for w,h in zip(om,hs)) for om in vertices)
        if all(0<=i<L for i in inds):yield inds

def cube(f,inds):
    z=1+0j
    for w,i in zip(vertices,inds):
        z*=f[i].conjugate() if sum(w)%2 else f[i]
    return z

def face_sums(f):
    L=len(f); S={}
    for x,a,b in product(range(L),repeat=3):
        aa,bb=a-x,b-x
        j=x+aa+bb
        if 0<=j<L:
            S[aa,bb]=S.get((aa,bb),0j)+f[x]*f[a].conjugate()*f[b].conjugate()*f[j]
    return S

def sq(z):return int(z.real)**2+int(z.imag)**2
for L in range(1,6):
    inds=list(cubes(L)); den=len(inds); N=16*L
    ck('indicator positive',den>0)
    for f in product((0j,)+units,repeat=L):
        terms=[cube(f,t) for t in inds]
        raw=sum(terms,0j)
        E=face_sums(f); e2=[sq(v) for v in E.values()]; en=sum(e2)
        ck('exact cube energy',raw==en)
        ck('normalized ratio bounded',0<=en<=den)
        ck('large face mean',max(e2,default=0)*N*N>=en)
        if en==den:
            ck('maximal cube saturation',all(z==1 for z in terms))
            ck('maximal unit modulus',all(sq(z)==1 for z in f))
            if L>=3:
                A=f[0]; B=f[1]*A.conjugate(); C=f[2]*A*f[1].conjugate()**2
                g=[A*B**n*C**(n*(n-1)//2) for n in range(L)]
                ck('exact quadratic representation',list(f)==g)
                ck('perfect inverse correlation',sum(z*w.conjugate() for z,w in zip(f,g))==L)
                for n in range(L-3):ck('third multiplicative derivative',f[n+3]*f[n+1]**3==f[n]*f[n+2]**3)
# Nontrivial quadratic examples on larger intervals, plus perturbed inputs.
r=Random(30086)
for _ in range(120):
    L=r.randrange(3,12); A,B,C=[r.choice(units) for _ in range(3)]
    f=[A*B**(n%4)*C**((n*(n-1)//2)%4) for n in range(L)]
    inds=list(cubes(L)); den=len(inds)
    ck('quadratic gives maximal U3',sum(cube(f,t) for t in inds)==den)
    n=r.randrange(L); f[n]=0j
    ck('nonunit perturbation strictly nonmaximal',sum(cube(f,t) for t in inds).real<den)
# Good-set bound for normalized energy, independently over exact rationals.
for _ in range(3000):
    u=[Q(r.randrange(21),20) for _ in range(r.randrange(1,40))]
    eta=Q(r.randrange(21),20)
    if sum(u)>=eta*len(u):
        ck('good shift density',sum(v>=eta/2 for v in u)>=eta*len(u)/2)
for k,v in sorted(counts.items()):print(f'{k}: {v} PASS')
print(f'TOTAL: {sum(counts.values())} PASS (exact model checks only)')
