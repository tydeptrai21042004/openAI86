#!/usr/bin/env python3
"""Exact model tests for V18; not a Lean kernel certificate."""
from fractions import Fraction as Q
from random import Random
from itertools import permutations, product
from test_v15_actual_projection_blocks import pmat, mv, row_eval, e, sub, matmul
rng=Random(180086)
counts={}
def ck(kind, ok):
    if not ok: raise AssertionError(kind)
    counts[kind]=counts.get(kind,0)+1

def apply(m,n,x):
    for i in range(m): x=mv(pmat(i%4,n),x)
    return x

def diff(x,y): return tuple(a-b for a,b in zip(x,y))
for _ in range(220):
    k=rng.randrange(0,6); T=rng.randrange(1<<k)
    x=tuple(Q(rng.randrange(-9,10),rng.randrange(1,7)) for _ in range(3))
    depths=[rng.randrange(T+1) for _ in range(3)]
    for m in range(9):
        energy=sum(row_eval(r,apply(m,n,x))**2 for r,n in enumerate(depths))
        ck('prefix',energy <= (k+1)**(2*m)*e(x))
        if m==0:
            ck('empty variation',all(apply(0,n,x)==x for n in range(T+1)))
            continue
        vals=[apply(m,n,x) for n in range(T+1)]
        v=sum(e(diff(vals[n+1],vals[n])) for n in range(T))
        ck('variation',v<=m*m*(k+1)**(2*(m-1))*e(x))
        if m>=2:
            for n in range(T):
                old=apply(m-1,n,x); new=apply(m-1,n+1,x)
                a=mv(pmat((m-1)%4,n+1),diff(new,old)); b=mv(sub(pmat((m-1)%4,n+1),pmat((m-1)%4,n)),old)
                z=tuple(u+w for u,w in zip(a,b))
                ck('ordered variation identity',z==diff(vals[n+1],vals[n]))
                ck('weighted CS',(m-1)*e(z)<=m*e(a)+(m-1)*m*e(b))
for i,a,b in permutations(range(4),3):
    w=Q(i-b,b-a); v=Q(a-i,b-a)
    ck('rational slot weights',1+w+v==0 and i+a*w+b*v==0)
    for _ in range(35):
        x,t,l=[Q(rng.randrange(-10,11),rng.randrange(1,8)) for _ in range(3)]
        ck('quadratic separation',l*(x+i*t)**2+w*l*(x+a*t)**2+v*l*(x+b*t)**2==l*(i-a)*(i-b)*t*t)
for x,a,b,c in product(range(-3,4),repeat=4):
    u,v,w,z=x,x+a,x+b,x+c
    ck('low inverse',(u,v-u,w-u,z-u)==(x,a,b,c))
    u,v,w,z=x+a+b+c,x+b+c,x+a+c,x+a+b
    ck('high inverse',(v+w+z-2*u,u-v,u-w,u-z)==(x,a,b,c))
for N in range(1,101):
    F=set(range(N))
    for _ in range(50):
        s=10*N//11+1; g=(9*N+9)//10
        A=set(rng.sample(range(N),s)); B=set(rng.sample(range(N),s)); G=set(rng.sample(range(N),g))
        ck('good primary overlap',bool(A&B&G))
print(counts)
print('V18 exact model checks:',sum(counts.values()))
